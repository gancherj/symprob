module Crypto.DistExample where
import Control.Monad
import qualified Data.Map.Strict as Map
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Crypto.Prot as P
import qualified Data.List as List
import Crypto.Dist 
{-
   library for writing probabilistic programs, where some of the distributions are underspecified. 
   the idea is that I can write probabilistic programs that can call unspecified algorithms. And I can partially apply computations to other computations. 

   The reason to do this is to symbolically verify equivalence of finite distributions. This can be done much more efficiently than in FCF.

   The backend can be sbv, which provides a binding to Z3 for theory of reals.

   Unknown probabilistic computations are functions state -> input -> distr on (new state, output).
-}


chooseWith :: [SReal] -> Dist SWord8
chooseWith rs = Dist.fromFreqs $ zip [1,2,3,4,5] rs


guessProb :: (EqSymbolic a, Mergeable a) => Dist a -> Dist a -> Probability
guessProb dA dB = 
    (\(x,y) -> x .== y) .?? exp dA dB
        where
            exp :: Dist a -> Dist a -> Dist (a,a)
            exp da db = do
                x <- da
                y <- db
                return (x,y)

constrainProb :: [SReal] -> Symbolic ()
constrainProb rs = do
    forM rs (\r -> do {constrain $ r .>= 0; constrain $ r .<= 1})
    constrain $ (sum rs) .== 1

trans :: Dist SWord8 -> Dist SWord8
trans d = 
    let pairs = Dist.decons d in
    Dist.fromFreqs (t pairs)
        where t :: [(SWord8, SReal)] -> [(SWord8, SReal)]
              t [] = []
              t ((x,y):ps) = 
                  let ys = t ps
                      e = ite (x .== 2) (3) (ite (x .== 3) (2) x) in
                  ((e,y) : ys)


f :: SWord64
f = uninterpret "f"

ex :: IO ()
ex = do
    r <- sat $ \r1 r2 r3 r4 r5 -> do
        let rs = [r1, r2, r3, r4, r5] 
            dist1 = chooseWith rs
            dist2 = chooseWith [0,1,0,0,0]
            x = guessProb (trans dist1) dist2
        constrainProb rs
        return $ x .== 1
    putStrLn $ show $ r 
    putStrLn . show =<< prove (f .== f)
    putStrLn "hello world"
