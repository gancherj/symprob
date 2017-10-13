module Main where
import Control.Monad
import Data.SBV
import qualified Crypto.Prot as Prot
import qualified Crypto.Dist as Dist


testDist :: (SBool -> Dist.Dist SBool) -> (SBool -> Dist.Dist SBool) -> Dist.Dist SBool
testDist f g = do
    x <- f false
    x' <- f true
    y <- g false
    y' <- g true
    return $ x .== y &&& x' .== y'



tst :: Symbolic Dist.Probability
tst = do
    f <- (Dist.genReaction :: Symbolic (SBool -> Dist.Dist SBool))
    g <- (Dist.genReaction :: Symbolic (SBool -> Dist.Dist SBool))

    return $ true Dist..??= (testDist f g)
    

t :: Symbolic SBool
t = do
    out_dist <- Prot.runIdealCrupt2 false
    let x = (Prot.msgOutput false, Prot.msgErr) Dist..??= out_dist
        y = (\_ -> true) Dist..?? out_dist
        z = (\((m0, m1), _) -> m0 .== literal Prot.Output ==> m1 .== true) Dist..?? out_dist
    return $ z .== 1

t2 :: Symbolic SBool
t2 = do
    a <- Prot.genAdv 2
    return $ Prot.equalParties a (Prot.honestPartyRightIdeal true)

main = do
    -- putStrLn . show =<< prove Prot.honestIdealCorrect
    -- putStrLn . show =<< prove Prot.honestRealCorrect

    putStrLn "prove:"
    putStrLn . show =<< sat (\x -> do
        y <- Prot.rpsSecure x
        return (bnot y)) 
