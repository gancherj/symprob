module Crypto.Prot where
import Control.Monad
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Data.List as List
import Crypto.Dist
import Crypto.Util
import qualified Data.Map.Strict as Map


type Party m s = (m,s) -> Dist (m,s)

instNullState :: s -> Party m (SWord8) -> Party m (SWord8, s)
instNullState snil f = \(m,(s0, s1)) -> do
    (m', _) <- f (m, s0)
    return (m', (s0 + 1, snil))

data ProtMsg = Play | Open | Ok | Result | Output | Err | Opened
mkSymbolicEnumeration ''ProtMsg

instance Enumerable ProtMsg where
    enumerate = [Play, Open, Ok, Result, Output, Err, Opened]

type SProtMsg = SBV ProtMsg

type Msg = (SProtMsg, SBool)


genAdv :: Integer -> Symbolic (Party Msg SWord8) 
genAdv bound = do
    reactions <- genReactions bound
    let pairs = zip (map (sFromIntegral . literal) [0..(bound - 1)]) reactions
        reax (i :: SWord8) inp = map (\(j, reac) -> (i .== j, do { m <- reac inp; return (m, i+1) } )) pairs
    return $ \(m, i) -> symSwitch (reax i m) (error "hello darkness my old friend")

equalParties :: Party Msg SWord8 -> Party Msg SWord8 -> SBool
equalParties p1 p2 =
    foldl (\acc p -> acc &&& seqDist (p1 p) (p2 p)) true enumerate

msgPlay :: SBool -> Msg
msgPlay a = (literal Play, a)

msgOpen :: Msg
msgOpen = (literal Open, false)

msgOk :: Msg
msgOk = (literal Ok, false)

msgResult :: SBool -> Msg
msgResult a = (literal Result, a)

msgOutput :: SBool -> Msg
msgOutput a = (literal Output,a)

msgErr :: Msg
msgErr = (literal Err, false)


msgOpened :: SBool -> Msg
msgOpened i = (literal Opened, i)


{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to A
   A: output result
   F: send result to B
   B : output result
-}


honestPartyLeftIdeal :: SBool -> Party Msg SWord8
honestPartyLeftIdeal inp ((m0, m1), i) =
        symSwitch [
            ((i .== 0), Dist.certainly $ (msgPlay inp, 1)),
            ((i .== 1) &&& (m0 .== literal Result), Dist.certainly $ (msgOutput m1, 2))]
            (Dist.certainly $ (msgErr, i + 1))

honestPartyRightIdeal :: SBool -> Party Msg SWord8
honestPartyRightIdeal inp ((m0, m1), i) =
        symSwitch [
            ((i .== 0) &&& ((m0, m1) .== msgOk), Dist.certainly $ (msgPlay inp, 1)),
            ((i .== 1) &&& (m0 .== literal Result), Dist.certainly $ (msgOutput m1, 2))]
            (Dist.certainly $ (msgErr, i + 1))

idealFunc :: Party Msg (SWord8, SBool, SBool)
idealFunc ((m0, m1), (i, p1, p2)) =
        symSwitch [
            ((i .== 0) &&& (m0 .== literal Play), Dist.certainly $ (msgOk, (1, m1, p2))),
            ((i .== 1) &&& (m0 .== literal Play), Dist.certainly $ (msgResult (m1 <+> p1), (2, p1, m1))),
            ((i .== 2) &&& (m0 .== literal Ok), Dist.certainly $ (msgResult (p1 <+> p2), (3, p1, p2)))]
            (Dist.certainly (msgErr, (i+1, false, false)))

runIdeal :: a -> b -> Party Msg a -> Party Msg b -> Dist (Msg, Msg)
runIdeal a b p1 p2 = do
    (m,s11) <- p1 (msgOk, a)
    (m,sf1) <- idealFunc (m, (0, false, false))
    (m, s21) <- p2 (m, b)
    (m, sf2) <- idealFunc (m, sf1)
    (out1, s12) <- p1 (m, s11)
    (m, _) <- idealFunc (msgOk, sf2)
    (out2, _) <- p2 (m, s21)
    return (out1, out2)

honestIdealCorrect :: SBool -> SBool -> SBool
honestIdealCorrect i1 i2 = (((msgOutput (i1 <+> i2)), (msgOutput (i1 <+> i2))) .??= (runIdeal 0 0 (honestPartyLeftIdeal i1) (honestPartyRightIdeal i2))) .== 1

runIdealCrupt2 :: SBool -> Symbolic (Dist (Msg, Msg))
runIdealCrupt2 i1 = do
    a <- genAdv 2
    return $ runIdeal 0 0 (honestPartyLeftIdeal i1) a

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

honestPartyLeftReal :: SBool -> Party Msg SWord8
honestPartyLeftReal inp ((m0, m1), i) =
        symSwitch [
            ((i .== 0) &&& ((m0, m1) .== msgOk), Dist.certainly $ (msgPlay inp, 1)),
            ((i .== 1) &&& ((m0, m1) .== msgOk), Dist.certainly $ (msgOpen, 2)),
            ((i .== 2) &&& (m0 .== literal Opened), Dist.certainly $ (msgOutput (inp <+> m1), 3))]
            (Dist.certainly $ (msgErr, i+1))

honestPartyRightReal :: SBool -> Party Msg (SWord8, SBool)
honestPartyRightReal inp ((m0, m1), (i, o)) =
        symSwitch [
            ((i .== 0) &&& ((m0, m1) .== msgOk), Dist.certainly $ (msgPlay inp, (1, o))),
            ((i .== 1) &&& (m0 .== literal Opened), Dist.certainly $ (msgOpen, (2, m1))),
            ((i .== 2) &&& ((m0, m1) .== msgOk), Dist.certainly $ (msgOutput (inp <+> o), (4, o)))]
            (Dist.certainly $ (msgErr, (i+1, false)))

fComm :: Party Msg (SWord8, SBool)
fComm ((m0, m1), (i,o)) =
        symSwitch [
            ((i .== 0) &&& (m0 .== literal Play), Dist.certainly $ (msgOk, (1, m1))),
            ((i .== 1) &&& ((m0, m1) .== msgOpen), Dist.certainly $ (msgOpened o, (2, o)))]
        (Dist.certainly $ (msgErr, (i+1, o)))

runReal :: a -> b ->  Party Msg a -> Party Msg b -> Dist (Msg, Msg)
runReal inita initb p1 p2 = do
    (m, sa1) <- p1 (msgOk, inita)
    (m, sf11) <- fComm (m, (0, false))
    (m, sb1) <- p2 (m, initb)
    (m, sf21) <- fComm (m, (0, false))
    (m, sa2) <- p1 (m, sa1)
    (m, sf12) <- fComm (m, sf11)
    (m, sb2) <- p2 (m, sb1)
    (m, sf22) <- fComm (m, sf21)
    (out1, _) <- p1 (m, sa2)
    (out2, _) <- p2 (msgOk, sb2)
    return (out1, out2)

honestRealCorrect :: SBool -> SBool -> SBool
honestRealCorrect i1 i2 = (((msgOutput (i1 <+> i2)), (msgOutput (i1 <+> i2))) .??= (runReal 0 (0, false) (honestPartyLeftReal i1) (honestPartyRightReal i2))) .== 1
    
simulatorRight :: Party Msg (SWord8, SBool) -> Party Msg ((SWord8, SBool), SWord8, SBool)
simulatorRight adv ((m0, m1), (advs, i, o)) = 
    symSwitch [
        (i .== 0 &&& (m0 .== literal Ok), do
            ((advm0, advm1), advs) <- adv (msgOk, (0, false))
            return $ symSwitch [
                (advm0 .== literal Play, (msgPlay advm1, (advs, 1, advm1)))]
                ((msgErr, (advs, 1, o)))),
        (i .== 1 &&& (m0 .== literal Result), do
            ((advm0, advm1), advs') <- adv ((msgOpened (o <+> m1)), advs) 
            symSwitch [
                ((advm0, advm1) .== msgOpen, do
                    ((advm0, advm1), _) <- adv (msgOk, advs')
                    return $ symSwitch [
                        ((advm0 .== literal Output), (msgOutput advm1, (advs', 2, o)))]
                        ((msgErr, (advs, 2, o))))
                ]
                (Dist.certainly $ (msgErr, (advs, 2, o))))]
        (Dist.certainly $ (msgErr, (advs, 2, o)))

simulatorRightIncorrect :: Party Msg (SWord8, SBool) -> Party Msg ((SWord8, SBool), SWord8, SBool)
simulatorRightIncorrect adv ((m0, m1), (advs, i, o)) = 
    symSwitch [
        (i .== 0 &&& (m0 .== literal Ok), do
            ((advm0, advm1), advs) <- adv (msgOk, (0, false))
            symSwitch [
                (advm0 .== literal Play, Dist.certainly $ (msgPlay advm1, (advs, 1, advm1)))]
                (Dist.certainly $ (msgErr, (advs, 1, o)))),
        (i .== 1 &&& (m0 .== literal Result), do
            ((advm0, advm1), advs') <- adv ((msgOpened (o <+> m1)), advs) 
            symSwitch [
                ((advm0, advm1) .== msgOpen, do
                    ((advm0, advm1), _) <- adv (msgOk, advs')
                    symSwitch [
                        ((advm0 .== literal Output), Dist.certainly $ (msgOutput advm1, (advs', 2, o)))]
                        (Dist.certainly $ (msgErr, (advs, 2, o))))
                ]
                (Dist.certainly $ (msgErr, (advs, 2, o))))]
        (Dist.certainly $ (msgErr, (advs, 2, o)))



rpsSecure :: SBool -> SBool -> Symbolic SBool
rpsSecure i i2 = do
    a <- genAdv 3
    let d1 = (runReal 0 (0, false) a (honestPartyRightReal i2))
        d2 = (runIdeal 0 0 (honestPartyLeftIdeal i) (honestPartyRightIdeal i2))
    return $ seqDist d1 d2


                
           

