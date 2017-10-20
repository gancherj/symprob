module Crypto.Util where
import Data.SBV
import Data.SBV.Control
import System.IO.Unsafe


tr :: String -> a -> a
tr s a = (unsafePerformIO (putStrLn s)) `seq` a

symSwitch :: Mergeable a => [(SBool, a)] -> a -> a
symSwitch [] def = def 
symSwitch ((cond, a) : conds) def =
    ite cond a (symSwitch conds def)

symLift :: (Enumerable a, SymWord a) => (a -> SBool) -> SBV a -> SBool
symLift f =
    let tests x = map (\a -> (x .== literal a, (f a))) enumerate in
    \x -> symSwitch (init (tests x)) (snd (last (tests x)))

symLift2 :: (Enumerable a, SymWord a, Enumerable b, SymWord b) => (a -> b -> SBool) -> SBV a -> SBV b -> SBool
symLift2 f =
    let tests x y = map (\(a,b) -> (x .== literal a &&& y .== literal b, (f a b))) enumerate in
    \x y -> symSwitch (init (tests x y)) (snd (last (tests x y)))

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
