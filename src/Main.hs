module Main where
import Control.Monad
import Data.SBV
import Data.SBV.Control
import Crypto.Util
import qualified Numeric.Probability.Random as Rand
import qualified Crypto.Prot as Prot
import qualified Crypto.Dist as Dist
import qualified Data.Map.Strict as Map
import qualified Numeric.Probability.Distribution as Dist
import qualified Crypto.Party as Party
    
queryProt :: Symbolic ()
queryProt = do
    (d1, d2, x, a) <- (Prot.rpsSecure false false)
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
              av <- Dist.getReact a
              d1v <- Dist.getDist d1
              d2v <- Dist.getDist d2
              io $ putStrLn $ Dist.ppDist d1v
              io $ putStrLn $ Dist.ppDist d2v
              io $ do
                      (m1,m2, ms) <- Rand.run $ Rand.pick $ Prot.runRealWithAdv False av
                      (u1,u2, us) <- Rand.run $ Rand.pick $ Prot.runIdealWithAdv False av
                      putStrLn "Real:"
                      putStrLn $ show (m1, m2)
                      putStrLn "Ideal:"
                      putStrLn $ show (u1, u2)
                      putStrLn "Real trace:"
                      putStrLn $ show ms
                      putStrLn "Ideal trace:"
                      putStrLn $ show us
                      putStrLn "\n \n \n"

              return ()

   

main = do
    {-putStrLn . show =<< prove ( do
        x <- tst
        return $ x .== 1)


    putStrLn . show =<< prove Prot.honestIdealCorrect
    putStrLn . show =<< prove Prot.honestRealCorrect
    -}
    
    putStrLn "run:"
    runSMTWith z3 queryProt
    putStrLn . show =<< prove (symLift2 Prot.honestIdealCorrect)
    putStrLn . show =<< isVacuous (symLift2 Prot.honestIdealCorrect)
    putStrLn . show =<< prove (symLift2 Prot.honestRealCorrect)

    --putStrLn "sat:"
    --res <- sat t2
    --putStrLn $ show res
    {-
    putStrLn . show =<< prove (Dist.seqDist (Dist.certainly (false :: SBool)) (Dist.uniform [false, true]))
    -}

