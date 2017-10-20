module Main where
import Control.Monad
import Data.SBV
import Data.SBV.Control
import Crypto.Util
import qualified Crypto.Prot as Prot
import qualified Crypto.Dist as Dist
import qualified Data.Map.Strict as Map
import qualified Numeric.Probability.Distribution as Dist
    
queryProt :: Symbolic ()
queryProt = do
    (d1, d2, x, a) <- (Prot.rpsSecure false false)
    -- constrain $ ((\(x1,x2) -> (fst x1) .== literal Prot.Err) Dist..?? d1) .== ((\(x1,x2) -> (fst x1) .== literal Prot.Err) Dist..?? d2)
    -- constrain $ ((\(x1,x2) -> (fst x1) .== literal Prot.Err) Dist..?? d1) .== 1
    constrain $ x .== true
    query $ do
        cs <- checkSat
        case cs of
          Unk -> io $ putStrLn $ "unk"
          Unsat -> io $ putStrLn $ "unsat"
          Sat -> do
              io $ putStrLn $ "sat"
              xv <- getValue x
              d1v <- Dist.getDist d1
              d2v <- Dist.getDist d2
              ads <- Dist.getDist (a (Prot.msgOk, 0))
              io $ putStrLn $ "d1: " ++ (Dist.ppDist d1v)
              io $ putStrLn $ "d2: " ++ (Dist.ppDist d2v)
              io $ putStrLn $ "x: " ++ (show xv)
              io $ putStrLn $ "x: " ++ (Dist.ppDist ads)
              -- io $ putStrLn $ "a: " ++ (unwords (map (\m -> (Dist.ppDist (av m))) enumerate))
              return ()

   

main = do
    {-putStrLn . show =<< prove ( do
        x <- tst
        return $ x .== 1)


    putStrLn . show =<< prove Prot.honestIdealCorrect
    putStrLn . show =<< prove Prot.honestRealCorrect
    -}
    putStrLn "run:"
    runSMTWith z3{verbose=True} queryProt
    putStrLn . show =<< prove (symLift2 Prot.honestIdealCorrect)
    putStrLn . show =<< prove (symLift2 Prot.honestRealCorrect)


    --putStrLn "sat:"
    --res <- sat t2
    --putStrLn $ show res
    {-
    putStrLn . show =<< prove (Dist.seqDist (Dist.certainly (false :: SBool)) (Dist.uniform [false, true]))
    -}

