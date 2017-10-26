{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Crypto.Party where
import Crypto.Dist
import Crypto.Util
import Control.Monad
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist

type React p m s = StateT s (Dist.T p) m

--getReaction :: (Ord a, Enumerable a, Ord b) => (a -> React SReal m s) -> (a -> React AlgReal m s)
--getReaction f = do



newtype StageID = Stage Int
    deriving (Eq, Num, Ord, Show)

data Msg = Play Bool | Open | Ok | Result Bool | Output Bool | Err | Opened Bool
    deriving (Show, Ord, Eq)

instance Enumerable Msg where
    enumerate = [Open, Ok, Err] ++ (map Play enumerate) ++ (map Result enumerate) ++ (map Output enumerate) ++ (map Opened enumerate)

instance Enumerable StageID where
    enumerate = [0,1,2,3,4,5,6,7,8,9,10]

data Party p = forall s. Show s => Party {
    _state :: s,
    _react :: Num p => Msg -> React p Msg s
}

instance Show (Party p) where
    show _ = "<party>"



data Config p = Config {
    _pmap :: Map.Map String (Party p),
    _outs :: [(String, Msg)],
    _log :: [String]
}
    deriving (Show)

ppLog :: Config p -> String
ppLog (Config _ _ log) = foldl (\acc s -> (show s) ++ "\n" ++ acc) "" log


cfgLog :: Num p => String -> React p () (Config p)
cfgLog s = do
    (Config a b c) <- get
    put (Config a b (s : c))
    

runParty :: Num p => (String, Bool, Maybe Msg) -> Msg -> React p Msg (Config p)
runParty (id, isout, spec) m = do
    (Config pmap outs log) <- get
    case Map.lookup id pmap of
      Just (Party s f) -> do
          let md = case spec of
                    Just ms -> ms
                    Nothing -> m
          (m', s') <- lift $ runStateT (f md) s
          let outs' = if isout then ((id,m'):outs) else outs
          put $ Config (Map.insert id (Party s' f) pmap) outs' log
          cfgLog $ id ++ "(" ++ (show s) ++ ") : " ++ (show m')
          return m'
      _ -> fail "not found"

runProt :: Num p => [(String, Bool, Maybe Msg)] -> Msg -> React p () (Config p)
runProt [] _ = return ()
runProt (id : ids) curm = do
    m' <- runParty id curm
    runProt ids m'



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

runIdeal :: (Show s1, Show s2, Num p) => (s1, Msg -> React p Msg s1) -> (s2, Msg -> React p Msg s2) -> Dist.T p (Config p)
runIdeal (as, a) (bs, b) = do
    let parties = Map.fromList [("A", Party as a), ("B", Party bs b), ("F", Party (0, Nothing, Nothing) idealFunc)]
        cfg = Config parties [] []
        script = [("A", False, Nothing),
                  ("F", False, Nothing),
                  ("B", False, Nothing),
                  ("F", False, Nothing),
                  ("B", False, Nothing),
                  ("F", False, Nothing),
                  ("A", True, Nothing),
                  ("B", True, Just Ok)]
    execStateT (runProt script Ok) cfg


runHonestIdeal :: Num p => Bool -> Bool -> Dist.T p (Config p)
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

runReal :: (Show s1, Show s2, Num p) => (s1, Msg -> React p Msg s1) -> (s2, Msg -> React p Msg s2) -> Dist.T p (Config p)
runReal (sa, a) (sb, b) = 
    let parties = Map.fromList [("A", Party sa a), ("B", Party sb b), ("Fc1", Party (0, Nothing) fComm), ("Fc2", Party (0, Nothing) fComm)]
        cfg = Config parties [] []
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

runHonestReal :: Num p => Bool -> Bool -> Dist.T p (Config p)
runHonestReal i1 i2 = runReal (0, honestPartyLeftReal i1) ((0, Nothing), (honestPartyRightReal i2))

genAdv :: Integer -> Symbolic (Msg -> React SReal Msg StageID)
genAdv bound = do
    creactions <- (genDetReactions bound) :: Symbolic [Msg -> SymDist Msg]
    return $ \m -> do
        i <- get
        put $ i + 1
        let j' = min i (fromInteger (bound - 1))
        case j' of
          Stage j -> do
              m' <- lift $ (creactions !! j) m
              return m'

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

rpsSecure :: Bool -> Symbolic (SymDist (Msg, Msg), SymDist (Msg, Msg), SBool, Msg -> React SReal Msg StageID )
rpsSecure i1 = do
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

