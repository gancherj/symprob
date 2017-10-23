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

data ProtMsg = Play | Open | Ok | Result | Output | Err | Opened
    deriving (Eq, Show, Ord)

instance Enumerable ProtMsg where
    enumerate = [Play, Open, Ok, Result, Output, Err, Opened]

type Msg = (ProtMsg, Bool)

newtype StageID = Stage Int
    deriving (Eq, Num, Ord, Show)

instance Enumerable StageID where
    enumerate = [0,1,2,3,4,5,6,7,8,9,10]

data Party = forall s. Party {
    _state :: s,
    _react :: forall p. Num p => Msg -> React p Msg s
}



data Config = Config {
    _pmap :: Map.Map String Party,
    _outs :: [(String, Msg)],
    _log :: [String]
}

runParty :: Num p => (String, Bool) -> Msg -> React p Msg Config
runParty (id, isout) m = do
    (Config pmap outs log) <- get
    case Map.lookup id pmap of
      Just (Party s f) -> do
          (m', s') <- lift $ runStateT (f m) s
          let outs' = if isout then ((id,m'):outs) else outs
          put $ Config (Map.insert id (Party s' f) pmap) outs' log
          return m'
      _ -> fail "not found"

runProt :: Num p => [(String, Bool)] -> Msg -> React p () Config
runProt [] _ = return ()
runProt (id : ids) curm = do
    m' <- runParty id curm
    runProt ids m'


msgPlay :: Bool -> Msg
msgPlay a = (Play, a)

msgOpen :: Msg
msgOpen = (Open, False)

msgOk :: Msg
msgOk = (Ok, False)

msgResult :: Bool -> Msg
msgResult a = (Result, a)

msgOutput :: Bool -> Msg
msgOutput a = (Output,a)

msgErr :: Msg
msgErr = (Err, False)


msgOpened :: Bool -> Msg
msgOpened i = (Opened, i)

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
                (0, _) -> msgPlay inp
                (1, (Result, _)) -> msgOutput (snd m)
                _ -> msgErr

honestPartyRightIdeal :: Num p => Bool -> Msg -> React p Msg StageID
honestPartyRightIdeal inp m = do
    i <- get
    put $ i + 1
    return $ case (i,m) of
               (0, (Ok, _)) -> msgPlay inp
               (1, (Result, _)) -> msgOutput (snd m)
               _ -> msgErr


idealFunc :: Num p => Msg -> React p Msg (StageID, Bool, Bool)
idealFunc m = do
    (i, p1, p2) <- get
    case (i, m) of
      (0, (Play, _)) -> do
          put (1, (snd m), p2)
          return msgOk
      (1, (Play, _)) -> do
          put (2, p1, snd m)
          return (msgResult ((snd m) <+> p1))
      (2, (Ok, _)) -> do
          put (3, p1, p2)
          return (msgResult (p1 <+> p2))
      _ -> do
          put (i+1, p1, p2)
          return msgErr

runIdeal :: Num p => Bool -> Bool -> Dist.T p Config
runIdeal i1 i2 = do
    let parties = Map.fromList [("A", Party 0 (honestPartyLeftIdeal i1)), ("B", Party 0 (honestPartyRightIdeal i2)), ("F", Party (0, False, False) idealFunc)]
        cfg = Config parties [] []
        script = [("A", False),
                  ("F", False),
                  ("B", False),
                  ("F", False),
                  ("A", True),
                  ("F", False),
                  ("B", True)]
    execStateT (runProt script msgOk) cfg
        
