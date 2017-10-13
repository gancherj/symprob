module Crypto.Util where
import Data.SBV
import System.IO.Unsafe

tr :: String -> a -> a
tr s a = (unsafePerformIO (putStrLn s)) `seq` a

symSwitch :: Mergeable a => [(SBool, a)] -> a -> a
symSwitch [] def = def 
symSwitch ((cond, a) : conds) def =
    iteLazy cond a (symSwitch conds def)


class Enumerable a where
    enumerate :: [a]

instance (SymWord a, Enumerable a) => Enumerable (SBV a) where
    enumerate = map (\x -> literal x) enumerate

instance (Enumerable a, Enumerable b) => Enumerable (a,b) where
    enumerate = zip enumerate enumerate

instance Enumerable () where
    enumerate = [()]

instance Enumerable Bool where
    enumerate = [False, True]

instance Enumerable Word8 where
    enumerate = [0..255]
