module Main where
import Control.Monad
import Control.Monad.State
import Data.SBV
import Data.SBV.Control
import Crypto.Util
import qualified Numeric.Probability.Random as Rand
import qualified Crypto.Dist as Dist
import qualified Data.Map.Strict as Map
import qualified Numeric.Probability.Distribution as Dist
import qualified Crypto.Party as Party
import Crypto.RPS as RPS
import qualified Crypto.Sig as Sig

queryProt :: Bool -> Symbolic ()
queryProt c = do
    let f = if c then Sig.execConditioned else Sig.execUnconditioned
    (c1, d1, c2, d2, x) <- (f false)
    -- constrain $ ((\(x1,x2) -> (fst x1) .== literal Prot.Err) Dist..?? d1) .== ((\(x1,x2) -> (fst x1) .== literal Prot.Err) Dist..?? d2)
    -- constrain $ ((\(x1,x2) -> x1 == Prot.msgErr) Dist.?? d2) .== 1
    constrain $ x .== false
    query $ do
        cs <- checkSat
        case cs of
          Unk -> io $ putStrLn $ "unk"
          Unsat -> io $ putStrLn $ "unsat"
          Sat -> do
              io $ putStrLn $ "sat"
              return ()

rpsSecureWith :: Bool -> Symbolic SBool
rpsSecureWith i1 = do
    (_, _, x, a) <- (RPS.rpsExec i1)
    return x

rpsSecure :: Symbolic SBool
rpsSecure = do
    let bs = enumerate
    ys <- forM bs (\(b) -> rpsSecureWith b)
    return $ bAnd ys

main = do
    {-putStrLn . show =<< prove ( do
        x <- tst
        return $ x .== 1)
-}

    --putStrLn . show =<< prove Prot.honestIdealCorrect
    --putStrLn . show =<< prove Prot.honestRealCorrect
    
    --putStrLn . show =<< prove (Sig.honestIdealCorrect False) 
    --putStrLn "run:"
    --putStrLn . show =<< prove (rpsSecure)
    --putStrLn . show =<< prove (Party.rpsSecure True)
    runSMTWith z3 (queryProt False)
    runSMTWith z3 (queryProt True)
    --putStrLn . show =<< prove (symLift2 Prot.honestIdealCorrect)
    --putStrLn . show =<< isVacuous (symLift2 Prot.honestIdealCorrect)
    --putStrLn . show =<< prove (symLift2 Prot.honestRealCorrect)


