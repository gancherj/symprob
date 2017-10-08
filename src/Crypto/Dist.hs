module Crypto.Dist where
import Control.Monad
import qualified Numeric.Probability.Distribution as D
import Data.SBV

type Probability = SReal
type SDist a = SBV (D.T Probability a)
type Dist a = D.T Probability a

symFilter :: Mergeable a => (a -> SBool) -> [(a, SReal)] -> [(a, SReal)]
symFilter p [] = []
symFilter p ((x,y):xs) = 
    iteLazy (p x) ((x,y):ys) ys
        where
            ys = symFilter p xs

(.??) :: Mergeable a => (a -> SBool) -> Dist a -> Probability
(.??) p d = D.sumP $ symFilter p (D.decons d)

instance Floating AlgReal where 


