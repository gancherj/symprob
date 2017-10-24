module Crypto.Dist where
import Control.Monad
import qualified Numeric.Probability.Distribution as D
import Data.SBV
import Data.SBV.Control
import qualified Data.Map.Strict as Map
import Crypto.Util

type SymDist a = D.T SReal a
type ConcreteDist a = D.T AlgReal a


getDist :: (Ord a) => SymDist a -> Query (ConcreteDist a)
getDist d = do
    let pairs = D.decons d
    ps <- forM pairs (\(a,p) -> do
        pv <- getValue p
        return (a, pv))
    return $ D.norm $ D.fromFreqs ps

getReact :: (Ord a, Enumerable a, Ord b) => (a -> SymDist b) -> Query (a -> ConcreteDist b)
getReact f = do
    pairs <- forM enumerate (\a -> do {d <- getDist (f a); return (a, d)})
    let m = Map.fromList pairs
    return $ \a -> m Map.! a

ppReact :: (Enumerable a, Enumerable b, Show a, Show b, Ord b) => (a -> ConcreteDist b) -> String
ppReact f = do
    foldl (\acc a -> acc ++ "\n" ++ (show a) ++ " -> \n " ++ (ppDist (f a)) ++ "\n") "" enumerate

(??=) :: (Eq a, Num p) => a -> D.T p a -> p
(??=) a d = (\x -> x == a) D.?? d

constrainProb :: [SReal] -> Symbolic ()
constrainProb rs = do
    forM rs (\r -> do {constrain $ r .>= 0; constrain $ r .<= 1})
    constrain $ (sum rs) .== 1

constrainDet :: [SReal] -> Symbolic ()
constrainDet rs = do
    constrain $ bOr $ map (\r -> r .== 1) rs

instance Floating AlgReal where 


seqDist :: (Eq a, Enumerable a) => SymDist a -> SymDist a -> SBool
seqDist d1 d2 = foldl (\acc a -> acc &&& ((a ??= d1) .== (a ??= d2))) true enumerate

ppDist :: (Show p, Num p, Ord p, Ord a, Show a) => D.T p a -> String
ppDist d = D.pretty show d

genSymDist :: Enumerable a => Symbolic (SymDist a)
genSymDist = do
    let as = enumerate
    rs <- forM as (\a -> (free_ :: Symbolic SReal))
    constrainProb rs
    return $ D.fromFreqs $ zip as rs

genReaction :: (Eq a, Enumerable a, Enumerable b) => Symbolic (a -> SymDist b)
genReaction = do
    dists <- forM as (\a -> genSymDist)
    let pairs = zip as dists
    return $ \x -> go x pairs
        where
            as = enumerate
            go x [(y,d)] = d
            go x ((y, d) : ps) = if x == y then d else go x ps


genReactions :: (Eq a, Enumerable a, Enumerable b) => Integer -> Symbolic [a -> SymDist b]
genReactions i = mapM (\_ -> genReaction) [1..i]

genDetSymDist :: Enumerable a => Symbolic (SymDist a)
genDetSymDist = do
    let as = enumerate
    rs <- forM as (\a -> (free_ :: Symbolic SReal))
    constrainProb rs
    constrainDet rs
    return $ D.fromFreqs $ zip as rs

genDetReaction :: (Eq a, Enumerable a, Enumerable b) => Symbolic (a -> SymDist b)
genDetReaction = do
    dists <- forM as (\a -> genDetSymDist)
    let pairs = zip as dists
    return $ \x -> go x pairs
        where
            as = enumerate
            go x [(y,d)] = d
            go x ((y, d) : ps) = if x == y then d else go x ps

genDetReactions :: (Eq a, Enumerable a, Enumerable b) => Integer -> Symbolic [a -> SymDist b]
genDetReactions i = mapM (\_ -> genReaction) [1..i]

instance Mergeable a => Mergeable (D.T SReal a) where
    symbolicMerge w s (D.Cons a) (D.Cons b) = D.Cons $ symbolicMerge w s a b
