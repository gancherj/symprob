{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Crypto.Sig where
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

instance Enumerable StageID where
    enumerate = [0,1,2,3,4,5,6,7,8,9,10]

type M = Bool

data Msg = Send M | OkQuery M | Ok | Err | Output M | SignA M Bool
    deriving (Eq, Ord, Show)

instance Enumerable Msg where
    enumerate = [Ok, Err] ++ (map Send enumerate) ++ (map OkQuery enumerate) ++ (map Output enumerate) ++ (map (SignA True) enumerate) ++ (map (SignA False) enumerate)

honestIdealPartyA :: Num p => M -> Msg -> React p Msg ()
honestIdealPartyA inp m = do
    return $ Send inp

honestIdealPartyB :: Num p => Msg -> React p Msg ()
honestIdealPartyB m = 
    return $ case m of
      OkQuery _ -> Ok
      _ -> Err

honestIdealPartyC :: Num p => Msg -> React p Msg (StageID, Maybe M)
honestIdealPartyC m = do
    (i, ms) <- get
    case (i,m, ms) of
      (0, Send a, _) -> do
          put $ (i+1, Just a)
          return $ OkQuery a
      (1, Ok, Just r) -> return $ Output r
      _ -> return Err
      
runIdeal :: (Show s, Show s1, Num p) => (s1, Msg -> React p Msg s1) -> (s, Msg -> React p Msg s) -> Dist.T p (Config p Msg)
runIdeal (as, a) (bs, b) = do
    let cfg = initConfig $ Map.fromList [("A", Party as a), ("B", Party bs b), ("C", Party (0, Nothing) honestIdealPartyC)]
        script = [("A", False, Nothing),
                  ("C", False, Nothing),
                  ("B", False, Nothing),
                  ("C", True, Nothing)]
    execStateT (runProt script Ok) cfg

runHonestIdeal i = runIdeal ((), honestIdealPartyA i) ((), honestIdealPartyB)

honestIdealCorrect i = ((\c -> (_outs c) == [("C", Output i)]) Dist.?? ((runHonestIdeal i) :: SymDist (Config _ Msg))) .== 1

---
--

honestRealPartyA :: Num p => M -> Msg -> React p Msg ()
honestRealPartyA inp m = do
    return $ SignA inp True

honestRealPartyB :: Num p => Msg -> React p Msg ()
honestRealPartyB inp = return inp

honestRealPartyC :: Num p => Msg -> React p Msg ()
honestRealPartyC inp = return $ case inp of
                         SignA m True -> Output m
                         _ -> Err

runReal :: (Show s, Show s1, Num p) => (s1, Msg -> React p Msg s1) -> (s, Msg -> React p Msg s) -> Dist.T p (Config p Msg)
runReal (as, a) (bs, b) = do
    let cfg = initConfig $ Map.fromList [("A", Party as a), ("B", Party bs b), ("C", Party () honestRealPartyC)]
        script = [("A", False, Nothing),
                  ("B", False, Nothing),
                  ("C", True, Nothing)]
    execStateT (runProt script Ok) cfg

simulatorRight :: Num p => (Msg -> React p Msg StageID) -> Msg -> React p Msg StageID
simulatorRight adv inp = do
    i <- get
    case inp of
      OkQuery m -> do
          advm <- lift $ evalStateT (adv (SignA m True)) i
          case advm of
            SignA fm True ->
                return Ok
            _ -> return Err
      _ -> return Err

execUnconditioned :: M -> Symbolic (SymDist (Config SReal Msg), SymDist Msg, SymDist (Config SReal Msg), SymDist Msg, SBool)
execUnconditioned i = do
    a <- genAdv 1
    let c1 = runReal ((), honestIdealPartyA i) (0, a)
        c2 = runIdeal ((), honestRealPartyA i) (0, simulatorRight a)
        d cd = do
            c <- cd
            return $ snd $ head $ (_outs c)
        d1 = d c1
        d2 = d c2
    return $ (c1, d1, c2, d2, seqDist d1 d2)

realCfgGood :: Config p Msg -> Bool
realCfgGood cfg = 
    case (_log cfg) of
      [("A", m1), ("B", m2), ("C", m3)] ->
          case m2 of
            (SignA m True) ->
                case m1 of
                  (SignA m' True) -> m == m'
                  _ -> False
            _ -> True
      _ -> error "bad log"


execConditioned :: M -> Symbolic (SymDist (Config SReal Msg), SymDist Msg, SymDist (Config SReal Msg), SymDist Msg, SBool)
execConditioned i = do
    a <- genAdv 1
    let c1 = runReal ((), honestIdealPartyA i) (0, a)
        c2 = runIdeal ((), honestRealPartyA i) (0, simulatorRight a)
        d cd = do
            c <- cd
            return $ snd $ head $ (_outs c)
        d1 = d c1
        d2 = d c2
    return $ (c1, d1, c2, d2, ((realCfgGood Dist.?? c1) .== 1) ==> seqDist d1 d2)

