module Crypto.Dist where
import Control.Monad
import qualified Numeric.Probability.Distribution as D
import Data.SBV
import Data.SBV.Control
import qualified Data.Map.Strict as Map
import Crypto.Util

type Probability = SReal
type SDist a = SBV (D.T Probability a)
type Dist a = D.T Probability a
type ConcreteDist a = D.T AlgReal a


getDist :: (Ord a) => Dist a -> Query (ConcreteDist a)
getDist d = do
    let pairs = D.decons d
    ps <- forM pairs (\(a,p) -> do
        pv <- getValue p
        return (a, pv))
    return $ D.norm $ D.fromFreqs ps

getReact :: (Ord a, Enumerable a, Ord b) => (a -> Dist b) -> Query (a -> ConcreteDist b)
getReact f = do
    pairs <- forM enumerate (\a -> do {d <- getDist (f a); return (a, d)})
    let m = Map.fromList pairs
    return $ \a -> m Map.! a

ppReact :: (Enumerable a, Enumerable b, Show a, Show b, Ord b) => (a -> ConcreteDist b) -> IO ()
ppReact f = do
    forM_ enumerate (\a -> do
        putStrLn $ (show a) ++ " -> \n " ++ (ppDist (f a))
        putStrLn $ "\n \n"
                    )




(??=) :: (Eq a) => a -> Dist a -> Probability
(??=) a d = (\x -> x == a) D.?? d

constrainProb :: [SReal] -> Symbolic ()
constrainProb rs = do
    forM rs (\r -> do {constrain $ r .>= 0; constrain $ r .<= 1})
    constrain $ (sum rs) .== 1

instance Floating AlgReal where 


seqDist :: (Eq a, Enumerable a) => Dist a -> Dist a -> SBool
seqDist d1 d2 = foldl (\acc a -> acc &&& ((a ??= d1) .== (a ??= d2))) true enumerate

ppDist :: (Show p, Num p, Ord p, Ord a, Show a) => D.T p a -> String
ppDist d = D.pretty show d

ppDist' :: (Show p, Show a) => D.T p a -> String
ppDist' d = go $ D.decons d
    where
        go [] = ""
        go (p:ps) = (show p) ++ "\n" ++ (go ps)

genSymDist :: Enumerable a => Symbolic (Dist a)
genSymDist = do
    let as = enumerate
    rs <- forM as (\a -> (free_ :: Symbolic SReal))
    constrainProb rs
    return $ D.fromFreqs $ zip as rs


genReaction :: (Eq a, Enumerable a, Enumerable b) => Symbolic (a -> Dist b)
genReaction = do
    dists <- forM as (\a -> genSymDist)
    let pairs = zip as dists
    return $ \x -> go x pairs
        where
            as = enumerate
            go x [(y,d)] = d
            go x ((y, d) : ps) = if x == y then d else go x ps


genReactions :: (Eq a, Enumerable a, Enumerable b) => Integer -> Symbolic [a -> Dist b]
genReactions i = mapM (\_ -> genReaction) [1..i]


instance Mergeable a => Mergeable (D.T Probability a) where
    symbolicMerge w s (D.Cons a) (D.Cons b) = D.Cons $ symbolicMerge w s a b
