module Main where
import Control.Monad
import Control.Monad.State
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
    (d1, d2, x, a) <- (Prot.rpsSecure false)
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

queryNewProt :: Symbolic ()
queryNewProt = do
    (d1, d2, x, a) <- (Party.rpsSecure false)
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
              av' <- Dist.getReact (\(m,s) -> runStateT (a m) s)
              let av m = do
                          i <- get
                          (m',s) <- lift $ av' (m, i)
                          put s
                          return m'
              io $ forM [0..3] $ \_ -> do
                  cfgr <- Rand.run $ Rand.pick (Party.runReal (0, Party.honestPartyLeftReal False) (0, av))
                  cfgi <- Rand.run $ Rand.pick (Party.runIdeal (0, Party.honestPartyLeftIdeal False) ((0, False), Party.simulatorRight av))
                  putStrLn "Real: "
                  putStrLn $ Party.ppLog cfgr
                  putStrLn "Ideal: "
                  putStrLn $ Party.ppLog cfgi
                  return ()
              return ()

rpsSecureWith :: Bool -> Symbolic SBool
rpsSecureWith i1 = do
    (_, _, x, a) <- (Prot.rpsSecure i1)
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
    
    
    --putStrLn "run:"
    --putStrLn . show =<< prove (rpsSecure)
    --putStrLn . show =<< prove (Party.rpsSecure True)
    runSMTWith z3 queryNewProt
    --putStrLn . show =<< prove (symLift2 Prot.honestIdealCorrect)
    --putStrLn . show =<< isVacuous (symLift2 Prot.honestIdealCorrect)
    --putStrLn . show =<< prove (symLift2 Prot.honestRealCorrect)


