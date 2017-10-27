{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Crypto.RPS where
import Crypto.Dist
import Crypto.Util
import Control.Monad
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import Crypto.Party


newtype StageID = Stage Int
    deriving (Eq, Num, Ord, Show, Real, Enum, Integral)

data Msg = Play Bool | Open | Ok | Result Bool | Output Bool | Err | Opened Bool
    deriving (Show, Ord, Eq)

instance Enumerable Msg where
    enumerate = [Open, Ok, Err] ++ (map Play enumerate) ++ (map Result enumerate) ++ (map Output enumerate) ++ (map Opened enumerate)

instance Enumerable StageID where
    enumerate = [0,1,2,3,4,5,6,7,8,9,10]

{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to A
   A: output result
   F: send result to B
   B : output result
-}

honestPartyLeftIdeal :: Num p => Bool -> Msg -> React p Msg StageID
honestPartyLeftIdeal inp m = do
    i <- get
    put $ i + 1
    return $ case (i, m) of
                (0, _) -> Play inp
                (1, (Result m1)) -> Output m1
                _ -> Err

honestPartyRightIdeal :: Num p => Bool -> Msg -> React p Msg (StageID, Maybe Bool)
honestPartyRightIdeal inp m = do
    (i, s) <- get
    (m',s') <- case (i,m, s) of
                 (0, Ok, _) -> return (Play inp, s)
                 (1, Result m1, _) -> return (Ok, Just m1)
                 (2, Ok, Just b) -> return (Output b, Just b)
                 _ -> return (Err, s)
    put (i + 1, s')
    return m'

-- the below can be rewritten more succinctly using lenses

idealFunc :: Num p => Msg -> React p Msg (StageID, Maybe Bool, Maybe Bool)
idealFunc m = do
    (i, p1, p2) <- get
    let (m', p1', p2') = case (i, m, p1, p2) of
                              (0, Play m1, _, _) -> (Ok, Just m1, p2)
                              (1, Play m1, Just a, _) -> (Result (m1 <+> a), p1, Just m1)
                              (2, Ok, Just a, Just b) -> (Result (a <+> b), p1, p2)
                              _ -> (Err, p1, p2)
    put $ (i+1, p1', p2')
    return m'

runIdeal :: (Show s1, Show s2, Num p) => (s1, Msg -> React p Msg s1) -> (s2, Msg -> React p Msg s2) -> Dist.T p (Config p Msg)
runIdeal (as, a) (bs, b) = do
    let cfg = initConfig $ Map.fromList [("A", Party as a), ("B", Party bs b), ("F", Party (0, Nothing, Nothing) idealFunc)]
        script = [("A", False, Nothing),
                  ("F", False, Nothing),
                  ("B", False, Nothing),
                  ("F", False, Nothing),
                  ("B", False, Nothing),
                  ("F", False, Nothing),
                  ("A", True, Nothing),
                  ("B", True, Just Ok)]
    execStateT (runProt script Ok) cfg


runHonestIdeal :: Num p => Bool -> Bool -> Dist.T p (Config p Msg)
runHonestIdeal i1 i2 = runIdeal (0, honestPartyLeftIdeal i1) ((0, Nothing), honestPartyRightIdeal i2) 
        

honestPartyLeftReal :: Num p => Bool -> Msg -> React p Msg StageID
honestPartyLeftReal inp m = do
    i <- get
    put $ i + 1
    return $ case (i,m) of
               (0, Ok) -> Play inp
               (1, Ok) -> Open
               (2, Opened m1) -> Output (inp <+> m1)
               _ -> Err

honestPartyRightReal :: Num p => Bool -> Msg -> React p Msg (StageID, Maybe Bool)
honestPartyRightReal inp m = do
   (i, o) <- get
   let (m', o') = case (i,m) of
                   (0, Ok) -> (Play inp, o)
                   (1, Opened m1) -> (Open, Just m1)
                   (2, Ok) | Just b <- o -> (Output (inp <+> b), o)
                   _ -> (Err, o)
   put $ (i+1, o')
   return m'

fComm :: Num p => Msg -> React p Msg (StageID, Maybe Bool)
fComm m = do
    (i,o) <- get
    let (m',o') = case (i,m) of
                    (0, Play m1) -> (Ok, Just m1)
                    (1, Open) | Just b <- o -> (Opened b, o)
                    _ -> (Err, o)
    put (i+1, o')
    return m'

runReal :: (Show s1, Show s2, Num p) => (s1, Msg -> React p Msg s1) -> (s2, Msg -> React p Msg s2) -> Dist.T p (Config p Msg)
runReal (sa, a) (sb, b) = 
    let cfg = initConfig $ Map.fromList [("A", Party sa a), ("B", Party sb b), ("Fc1", Party (0, Nothing) fComm), ("Fc2", Party (0, Nothing) fComm)]
        script = [("A", False, Nothing),
                  ("Fc1", False, Nothing),
                  ("B", False, Nothing),
                  ("Fc2", False, Nothing),
                  ("A", False, Nothing),
                  ("Fc1", False, Nothing),
                  ("B", False, Nothing),
                  ("Fc2", False, Nothing),
                  ("A", True, Nothing),
                  ("B", True, Just Ok)] in
    execStateT (runProt script Ok) cfg

runHonestReal :: Num p => Bool -> Bool -> Dist.T p (Config p Msg)
runHonestReal i1 i2 = runReal (0, honestPartyLeftReal i1) ((0, Nothing), (honestPartyRightReal i2))


simulatorRight :: Num p => (Msg -> React p Msg StageID) -> (Msg -> React p Msg (StageID, Bool))
simulatorRight adv m = do
    (i, o) <- get
    (m', o') <- case (i,m) of
                  (0, Ok) -> do
                      advm <- lift $ evalStateT (adv Ok) i
                      case advm of
                        Play advm1 -> return (Play advm1, advm1)
                        _ -> return (Err, o)
                  (1, Result b) -> do
                      m' <- lift $ evalStateT (adv (Opened (o <+> b))) i
                      case m' of
                        Open -> return (Ok, o)
                        _ -> return (Err, o)
                  (2, Ok) -> do
                      m'' <- lift $ evalStateT (adv Ok) i
                      return (m'', o)
                  _ -> return (Err, o)
    put $ (i+1, o')
    return m'

rpsExec :: Bool -> Symbolic (SymDist (Msg, Msg), SymDist (Msg, Msg), SBool, Msg -> React SReal Msg StageID )
rpsExec i1 = do
    a <- genAdv 4
    let cfgd1 = (runReal (0, honestPartyLeftReal i1) (0, a))
        cfgd2 = (runIdeal (0, honestPartyLeftIdeal i1) ((0, False), simulatorRight a))
        d1 = do
            c <- cfgd1
            return (snd $ (_outs c) !! 0, snd $ (_outs c) !! 1)
        d2 = do
            c <- cfgd2
            return (snd $ (_outs c) !! 0, snd $ (_outs c) !! 1)
    return $ (d1, d2, seqDist d1 d2, a)

