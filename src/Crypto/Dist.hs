module Crypto.Dist where
import Control.Monad
import qualified Numeric.Probability.Distribution as D
import Data.SBV
import Crypto.Util

type Probability = SReal
type SDist a = SBV (D.T Probability a)
type Dist a = D.T Probability a

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

constrainProb :: [SReal] -> Symbolic ()
constrainProb rs = do
    forM rs (\r -> do {constrain $ r .>= 0; constrain $ r .<= 1})
    constrain $ (sum rs) .== 1

instance Floating AlgReal where 

class Enumerable a where
    enumerate :: [a]

genSymDist :: Enumerable a => Symbolic (Dist a)
genSymDist = do
    let as = enumerate
    rs <- forM as (\a -> (free_ :: Symbolic SReal))
    constrainProb rs
    return $ D.Cons $ zip as rs



genReaction :: (EqSymbolic a, Enumerable a, Mergeable b, Enumerable b) => Symbolic (a -> Dist b)
genReaction = do
    dists <- forM as (\a -> genSymDist)
    let pairs = zip as dists
        tests x = map (\(a,b) -> (x .== a, b)) pairs
    return $ \(x :: a) -> symSwitch (tests x) (head dists) 
        where
            as = enumerate

instance Mergeable a => Mergeable (D.T Probability a) where
    symbolicMerge w s (D.Cons a) (D.Cons b) = D.Cons $ symbolicMerge w s a b
