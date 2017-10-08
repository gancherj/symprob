module Main where
import Control.Monad.Free
import qualified Data.Map.Strict as Map
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Data.List as List
{-
   library for writing probabilistic programs, where some of the distributions are underspecified. 
   the idea is that I can write probabilistic programs that can call unspecified algorithms. And I can partially apply computations to other computations. 

   The reason to do this is to symbolically verify equivalence of finite distributions. This can be done much more efficiently than in FCF.

   The backend can be sbv, which provides a binding to Z3 for theory of reals.

   Unknown probabilistic computations are functions state -> input -> distr on (new state, output).
-}

type Probability = SReal
type Dist a = Dist.T Probability a
type SymDist a = Symbolic (Dist a)

symFilter :: Mergeable a => (a -> SBool) -> [(a, SReal)] -> Symbolic [(a, SReal)]
symFilter p [] = return []
symFilter p ((x,y):xs) = do
    ys <- symFilter p xs
    return $ iteLazy (p x) ((x,y):ys) ys


(.??) :: Mergeable a => (a -> SBool) -> Dist a -> Symbolic Probability
(.??) p d = do
    probs <- symFilter p (Dist.decons d)
    return (Dist.sumP probs)
    

bitflip :: SymDist SBool
bitflip = do
    return $ Dist.uniform [true, false]

chooseWith :: SReal -> SymDist SBool
chooseWith r = do
    return $ Dist.choose r (true) (false)


p :: SReal -> Symbolic (Probability)
p r = do
    bf <- chooseWith (1-r) 
    cw <- chooseWith r 
    let (exp :: Dist (SBool, SBool)) = do
            x <- bf
            y <- cw
            return (x,y)
    (\(x,y) -> x .== y) .?? exp


q :: SReal -> Goal
q r = do
    x <- p r
    minimize "goal" x

main :: IO ()
main = do
    r <- sat $ \r -> do
        x <- p r
        return $ x .== 0.4
    r' <- sat (q 0)
    putStrLn $ show $ r
    putStrLn "hello world"
