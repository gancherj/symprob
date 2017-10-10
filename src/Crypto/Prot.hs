module Crypto.Prot where
import Control.Monad
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Data.List as List
import Crypto.Dist
import Crypto.Util
import qualified Data.Map.Strict as Map


type Party m s = (m,s) -> Dist (m,s)

type Msg = (SWord8, SBool)

msgPlay :: SBool -> Msg
msgPlay a = (0, a)

msgOpen :: Msg
msgOpen = (1, false)

msgOk :: Msg
msgOk = (2, false)

msgResult :: SBool -> Msg
msgResult a = (3, a)

msgOutput :: SBool -> Msg
msgOutput a = (4,a)

msgErr :: Msg
msgErr = (5, false)


{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to A
   A: output result
-}


honestPartyLeft :: SBool -> Party Msg SWord8
honestPartyLeft inp ((m0, m1), i) =
    Dist.certainly $ 
        symSwitch [
            ((i .== 0), (msgPlay inp, 1)),
            ((i .== 1) &&& (m0 .== 3), (msgOutput m1, 2))]
            ((msgErr, i + 1))

honestPartyRight :: SBool -> Party Msg SWord8
honestPartyRight inp ((m0, m1), i) =
    Dist.certainly $
        symSwitch [
            ((i .== 0) &&& ((m0, m1) .== msgOk), (msgPlay inp, 1))]
            ((msgErr, i + 1))

func :: Party Msg (SWord8, SBool)
func ((m0, m1), (i, p1)) =
    Dist.certainly $
        symSwitch [
            ((i .== 0) &&& (m0 .== 0), (msgOk, (1, m1))),
            ((i .== 1) &&& (m0 .== 0), (msgResult (m1 <+> p1), (2, p1)))]
            ((msgErr, (i+1, false)))

runHonest :: SBool -> SBool -> Dist (SWord8, SBool)
runHonest i1 i2 = do
    let p1 = honestPartyLeft i1
        p2 = honestPartyRight i2
    (m,s11) <- p1 (msgOk, 0)
    (m,sf1) <- func (m, (0, false))
    (m, s21) <- p2 (m, 0)
    (m, sf2) <- func (m, sf1)
    (m, s12) <- p1 (m, s11)
    return m

thmOk :: SBool -> SBool -> SBool
thmOk i1 i2 = ((msgOutput (i1 <+> i2)) .??= (runHonest i1 i2)) .== 1

