module Crypto.Dist where
import Control.Monad
import qualified Numeric.Probability.Distribution as D
import Data.SBV

type Probability = SReal
type SDist a = SBV (D.T Probability a)
type Dist a = D.T Probability a
    {-
symFilter :: Mergeable a => (a -> SBool) -> [(a, SReal)] -> [(a, SReal)]
symFilter p [] = []
symFilter p ((x,y):xs) = 
    iteLazy (p x) ((x,y):ys) ys
        where
            ys = symFilter p xs

(.??) :: Mergeable a => (a -> SBool) -> Dist a -> Probability
(.??) p d = D.sumP $ symFilter p (D.decons d)
-}

sumProbs :: Mergeable a => (a -> SBool) -> [(a, SReal)] -> SReal
sumProbs p [] = 0
sumProbs p ((x,y):xs) =
    ite (p x) (y + res) res
        where
            res = sumProbs p xs

(.??) :: Mergeable a => (a -> SBool) -> Dist a -> Probability
(.??) p d = sumProbs p (D.decons d)

(.??=) :: (EqSymbolic a, Mergeable a) => a -> Dist a -> Probability
(.??=) a d = (\x -> x .== a) .?? d


instance Floating AlgReal where 



class Enumerable a where
    enumerate :: [a]

