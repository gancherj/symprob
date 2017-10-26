{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Crypto.Party where
import Crypto.Dist
import Crypto.Util
import Control.Lens
import Control.Monad
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist

type React p m s = StateT s (Dist.T p) m


data Party p m = forall s. (Show m, Show s) => Party {
    _state :: s,
    _react :: Num p => m -> React p m s
}

instance Show (Party p m) where
    show _ = "<party>"

data Config p m = Config {
    _pmap :: Map.Map String (Party p m),
    _outs :: [(String, m)],
    _log :: [String],
    _bad :: Bool
}
    deriving (Show)

cfgLog :: Num p => String -> React p () (Config p m)
cfgLog s = do
    c <- get
    put $ c {_log = (s : (_log c))}

ppLog :: Config p m -> String
ppLog c = foldl (\acc s -> (show s) ++ "\n" ++ acc) "" (_log c)

initConfig :: Map.Map String (Party p m) -> Config p m
initConfig ps = Config ps [] [] False

runParty :: Num p => (String, Bool, Maybe m) -> m -> React p m (Config p m)
runParty (id, isout, spec) m = do
    (Config pmap outs log bad) <- get
    case Map.lookup id pmap of
      Just (Party s f) -> do
          let md = case spec of
                    Just ms -> ms
                    Nothing -> m
          (m', s') <- lift $ runStateT (f md) s
          let outs' = if isout then ((id,m'):outs) else outs
          put $ Config (Map.insert id (Party s' f) pmap) outs' log bad
          cfgLog $ id ++ "(" ++ (show s) ++ ") : " ++ (show m')
          return m'
      _ -> fail "not found"

runProt :: Num p => [(String, Bool, Maybe m)] -> m -> React p () (Config p m)
runProt [] _ = return ()
runProt (id : ids) curm = do
    m' <- runParty id curm
    runProt ids m'

