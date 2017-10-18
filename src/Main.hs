module Main where
import Control.Monad
import Data.SBV
import Data.SBV.Control
import qualified Crypto.Prot as Prot
import qualified Crypto.Dist as Dist
import qualified Numeric.Probability.Distribution as Dist

queryProt :: Symbolic ()
queryProt = do
    (d1, d2, x) <- (Prot.rpsSecure false false)
    constrain $ x .== false
    query $ do
        cs <- checkSat
        case cs of
          Unk -> io $ putStrLn $ "unk"
          Unsat -> io $ putStrLn $ "unsat"
          Sat -> do
              xv <- getValue x
              d1v <- Dist.getDist Prot.concretizeMsgPair d1
              d2v <- Dist.getDist Prot.concretizeMsgPair d2
              io $ putStrLn $ "d1: " ++ (Dist.ppDist d1v)
              io $ putStrLn $ "d2: " ++ (Dist.ppDist d2v)


main = do
    {-putStrLn . show =<< prove ( do
        x <- tst
        return $ x .== 1)


    putStrLn . show =<< prove Prot.honestIdealCorrect
    putStrLn . show =<< prove Prot.honestRealCorrect
    -}
    putStrLn "run:"
    runSMT queryProt


    --putStrLn "sat:"
    --res <- sat t2
    --putStrLn $ show res
    {-
    putStrLn . show =<< prove (Dist.seqDist (Dist.certainly (false :: SBool)) (Dist.uniform [false, true]))
    -}

