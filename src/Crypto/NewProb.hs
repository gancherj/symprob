module NewProb where
import Control.Monad

newtype Prob a = Prob { deprob :: (a -> Bool) -> Double }
