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


seqDist :: (EqSymbolic a, Enumerable a, Mergeable a) => Dist a -> Dist a -> SBool
seqDist d1 d2 = foldl (\acc a -> acc &&& ((a .??= d1) .== (a .??= d2))) true enumerate

ppDist :: Show a => Dist a -> String
ppDist d = show $ D.decons d

genSymDist :: Enumerable a => Symbolic (Dist a)
genSymDist = do
    let as = enumerate
    rs <- forM as (\a -> (free_ :: Symbolic SReal))
    constrainProb rs
    return $ D.fromFreqs $ zip as rs

genReaction :: (Show a, EqSymbolic a, Enumerable a, Mergeable b, Enumerable b) => Symbolic (a -> Dist b)
genReaction = do
    dists <- forM as (\a -> genSymDist)
    let pairs = zip as dists
        tests x = map (\(a,b) -> (x .== a, b)) pairs
    return $ \(x :: a) -> symSwitch (tests x) (error $ "bad switch: " ++ show x)
        where
            as = enumerate

genReaction2 :: (Show a, EqSymbolic a, Enumerable a, Mergeable b, Enumerable b) => Symbolic (a -> Dist b)
genReaction2 = do
    dists <- forM as (\a -> genSymDist)
    let pairs = zip as dists
        tests x = map (\(a,b) -> (x .== a, b)) pairs
    return $ \(x :: a) -> symSwitch (init (tests x)) (snd (last (tests x)))
        where
            as = enumerate

genReactions :: (Show a, EqSymbolic a, Enumerable a, Mergeable b, Enumerable b) => Integer -> Symbolic [a -> Dist b]
genReactions i = mapM (\_ -> genReaction2) [1..i]

instance Mergeable a => Mergeable (D.T Probability a) where
    symbolicMerge w s (D.Cons a) (D.Cons b) = D.Cons $ symbolicMerge w s a b
