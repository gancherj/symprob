module Main where
import Control.Monad
import Data.SBV
import qualified Crypto.Prot as Prot

    

main = do
    putStrLn . show =<< prove Prot.thmOk
