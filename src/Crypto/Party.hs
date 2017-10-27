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
    _log :: [(String, m)]
}
    deriving (Show)

instance Eq m => Eq (Config p m) where
    c1 == c2 =
        (_outs c1) == (_outs c2) && (_log c1) == (_log c2)

instance Eq m => Ord (Config p m) where
    compare _ _ = EQ


ppLog :: Show m => Config p m -> String
ppLog c = foldl (\acc s -> (show s) ++ "\n" ++ acc) "" (_log c)

updateParty :: Num p => String -> Party p m -> React p () (Config p m)
updateParty id p = do
    c <- get
    put $ c {_pmap = Map.insert id p (_pmap c)}

cfgLog :: Num p => String -> m -> React p () (Config p m)
cfgLog id m = do
    c <- get
    put $ c {_log = ((_log c) ++ [(id, m)])}

updateOut :: Num p => String -> m -> React p () (Config p m)
updateOut id m = do
    c <- get
    put $ c {_outs = ((_outs c) ++ [(id,m)])}


initConfig :: Map.Map String (Party p m) -> Config p m
initConfig ps = Config ps [] [] 

runParty :: Num p => (String, Bool, Maybe m) -> m -> React p m (Config p m)
runParty (id, isout, spec) m = do
    (Config pmap outs log ) <- get
    case Map.lookup id pmap of
      Just (Party s f) -> do
          let md = case spec of
                    Just ms -> ms
                    Nothing -> m
          (m', s') <- lift $ runStateT (f md) s
          if isout then updateOut id m' else return ()
          updateParty id (Party s' f)
          cfgLog id m'
          return m'
      _ -> fail "not found"

runProt :: Num p => [(String, Bool, Maybe m)] -> m -> React p () (Config p m)
runProt [] _ = return ()
runProt (id : ids) curm = do
    m' <- runParty id curm
    runProt ids m'

genAdv :: (Integral s, Enumerable s, Show s, Enumerable m, Eq m) => Integer -> Symbolic (m -> React SReal m s)
genAdv bound = do
    creactions <- (genDetReactions bound) 
    return $ \m -> do
        i <- get
        put $ i + 1
        let j = toInteger $ min i (fromInteger (bound - 1))
        m' <- lift $ (creactions !! (fromInteger j)) m
        return m'
