module Crypto.Util where
import Data.SBV
import System.IO.Unsafe

tr :: String -> a -> a
tr s a = (unsafePerformIO (putStrLn s)) `seq` a

symSwitch :: Mergeable a => [(SBool, a)] -> a -> a
symSwitch [] def = def 
symSwitch ((cond, a) : conds) def =
    ite cond a (symSwitch conds def)


class Enumerable a where
    enumerate :: [a]

instance (SymWord a, Enumerable a) => Enumerable (SBV a) where
    enumerate = [literal a | a <- enumerate]



instance (Enumerable a, Enumerable b) => Enumerable (a,b) where
    enumerate = [(a,b) | a <- enumerate, b <- enumerate]

instance Enumerable () where
    enumerate = [()]

instance Enumerable Bool where
    enumerate = [False, True]

instance Enumerable Word8 where
    enumerate = [0..255]
