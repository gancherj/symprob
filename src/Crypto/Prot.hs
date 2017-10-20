module Crypto.Prot where
import Control.Monad
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Data.List as List
import Crypto.Dist
import Crypto.Util
import qualified Data.Map.Strict as Map


type Party m s = (m,s) -> Dist (m,s)

instNullState :: s -> Party m (Word8) -> Party m (Word8, s)
instNullState snil f = \(m,(s0, s1)) -> do
    (m', a) <- f (m, s0)
    return (m', (a + 1, snil))

data ProtMsg = Play | Open | Ok | Result | Output | Err | Opened
    deriving (Eq, Show, Ord)

instance Enumerable ProtMsg where
    enumerate = [Play, Open, Ok, Result, Output, Err, Opened]

type Msg = (ProtMsg, Bool)

genAdv :: Integer -> Symbolic (Party Msg Word8)
genAdv bound = do
    creactions <- (genReactions bound) :: Symbolic [Msg -> Dist Msg]
    return $ \(m,i) -> do
        let j' = min i (fromInteger (bound - 1))
            (j :: Int) = fromInteger (toInteger j')
        m' <- (creactions !! j) m 
        return (m', i+1)

equalParties :: Party Msg Word8 -> Party Msg Word8 -> SBool
equalParties p1 p2 =
    foldl (\acc p -> acc &&& seqDist (p1 p) (p2 p)) true enumerate

msgPlay :: Bool -> Msg
msgPlay a = (Play, a)

msgOpen :: Msg
msgOpen = (Open, False)

msgOk :: Msg
msgOk = (Ok, False)

msgResult :: Bool -> Msg
msgResult a = (Result, a)

msgOutput :: Bool -> Msg
msgOutput a = (Output,a)

msgErr :: Msg
msgErr = (Err, False)


msgOpened :: Bool -> Msg
msgOpened i = (Opened, i)


{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to A
   A: output result
   F: send result to B
   B : output result
-}

bxor a b = if a == b then False else True

honestPartyLeftIdeal :: Bool -> Party Msg Word8
honestPartyLeftIdeal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, _) -> Dist.certainly $ (msgPlay inp, 1)
      (1, (Result, _)) -> Dist.certainly $ (msgOutput m1, 2)
      _ -> Dist.certainly $ (msgErr, i + 1)

honestPartyRightIdeal :: Bool -> Party Msg Word8
honestPartyRightIdeal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, msgOk) -> Dist.certainly $ (msgPlay inp, 1)
      (1, (Result, _)) -> Dist.certainly $ (msgOutput m1, 2)
      _ -> Dist.certainly $ (msgErr, i + 1)

idealFunc :: Party Msg (Word8, Bool, Bool)
idealFunc ((m0, m1), (i, p1, p2)) =
    case (i, (m0, m1)) of
      (0, (Play, _)) -> Dist.certainly $ (msgOk, (1, m1, p2))
      (1, (Play, _)) -> Dist.certainly $ (msgResult (m1 `bxor` p1), (2, p1, m1))
      (2, (Ok, _)) -> Dist.certainly $ (msgResult (p1 `bxor` p2), (3, p1, p2))
      _ -> Dist.certainly (msgErr, (i+1, p1, p2))

runIdeal :: a -> b -> Party Msg a -> Party Msg b -> Dist (Msg, Msg)
runIdeal a b p1 p2 = do
    (m,s11) <- p1 (msgOk, a)
    (m,sf1) <- idealFunc (m, (0, False, False))
    (m, s21) <- p2 (m, b)
    (m, sf2) <- idealFunc (m, sf1)
    (out1, s12) <- p1 (m, s11)
    (m, _) <- idealFunc (msgOk, sf2)
    (out2, _) <- p2 (m, s21)
    return (out1, out2)

honestIdealCorrect :: Bool -> Bool -> SBool
honestIdealCorrect i1 i2 = (((msgOutput (i1 `bxor` i2)), (msgOutput (i1 `bxor` i2))) ??= (runIdeal 0 0 (honestPartyLeftIdeal i1) (honestPartyRightIdeal i2))) .== 1


{-
    real protocol:
    A: activated, send play x to F1
    F1: send ok to B
    B: send play y to F2
    F2: send ok to A
    A: send open to F1
    F1: send x to B
    B: send open to F2
    F2: send y to A
    A: output result
    B: output result
-}

honestPartyLeftReal :: Bool -> Party Msg Word8
honestPartyLeftReal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, msgOk) -> Dist.certainly $ (msgPlay inp, 1)
      (1, msgOk) -> Dist.certainly $ (msgOpen, 2)
      (2, (Opened, _)) -> Dist.certainly (msgOutput (inp `bxor` m1), 3)
      _ -> Dist.certainly (msgErr, i+1)

honestPartyRightReal :: Bool -> Party Msg (Word8, Bool)
honestPartyRightReal inp ((m0, m1), (i, o)) =
    case (i, (m0, m1)) of
      (0, msgOk) -> Dist.certainly $ (msgPlay inp, (1, o))
      (1, (Opened, _)) -> Dist.certainly (msgOpen, (2, m1))
      (2, msgOk) -> Dist.certainly $ (msgOutput (inp `bxor` o), (4, o))
      _ -> Dist.certainly (msgErr, (i+1, false))

fComm :: Party Msg (Word8, Bool)
fComm ((m0, m1), (i,o)) =
    case (i, (m0, m1)) of
      (0, (Play, _)) -> Dist.certainly (msgOk, (1, m1))
      (1, msgOpen) -> Dist.certainly (msgOpened o, (2, o))
      _ -> Dist.certainly (msgErr, (i+1, o))

runReal :: a -> b ->  Party Msg a -> Party Msg b -> Dist (Msg, Msg)
runReal inita initb p1 p2 = do
    (m, sa1) <- p1 (msgOk, inita)
    (m, sf11) <- fComm (m, (0, False))
    (m, sb1) <- p2 (m, initb)
    (m, sf21) <- fComm (m, (0, False))
    (m, sa2) <- p1 (m, sa1)
    (m, sf12) <- fComm (m, sf11)
    (m, sb2) <- p2 (m, sb1)
    (m, sf22) <- fComm (m, sf21)
    (out1, _) <- p1 (m, sa2)
    (out2, _) <- p2 (msgOk, sb2)
    return (out1, out2)

honestRealCorrect :: Bool -> Bool -> SBool
honestRealCorrect i1 i2 = (((msgOutput (i1 `bxor` i2)), (msgOutput (i1 `bxor` i2))) ??= (runReal 0 (0, False) (honestPartyLeftReal i1) (honestPartyRightReal i2))) .== 1
     
simulatorRight :: Party Msg Word8 -> Party Msg (Word8, Word8, Bool)
simulatorRight adv ((m0, m1), (advs, i, o)) = 
    case (i, (m0, m1)) of
      (0, (Ok, _)) -> do
          ((advm0, advm1), advs') <- adv (msgOk, 0)
          case advm0 of
            Play -> Dist.certainly (msgPlay advm1, (advs', i+1, advm1))
            _ -> Dist.certainly (msgErr, (advs', i+1, o))
      (1, (Result, _)) -> do
          ((advm0, advm1), advs') <- adv (msgOpened (o `bxor` m1), advs)
          if (advm0, advm1) == msgOpen then
             do
                ((m0, m1), advs'') <- adv (msgOk, advs')
                return ((m0,m1), (advs'', i+1, o))
          else Dist.certainly (msgErr, (advs', i+1, o))

      _ -> Dist.certainly (msgErr, (advs, i+1, o))
                


runRPSSim :: Bool -> Bool -> Symbolic (Dist (Msg, Msg), Dist (Msg, Msg), Party Msg Word8)
runRPSSim i i2 = do
    a <- genAdv 3
    let d1 = (runReal 0 0 (honestPartyLeftReal i) a)
        d2 = (runIdeal 0 (0, 0, false) (honestPartyLeftIdeal i) (simulatorRight a))
    return (d1, d2, a)


rpsSecure :: Bool -> Bool -> Symbolic (Dist (Msg, Msg), Dist (Msg, Msg), SBool, Party Msg Word8)
rpsSecure i1 i2 = do
    (d1, d2, a) <- runRPSSim i1 i2
    return $ (d1, d2, seqDist d1 d2, a)

           
