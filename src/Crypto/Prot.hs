{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Crypto.Prot where
import Control.Monad
import Data.SBV
import qualified Numeric.Probability.Distribution as Dist
import qualified Data.List as List
import Crypto.Dist
import Crypto.Util
import qualified Data.Map.Strict as Map

newtype StageID = Stage Int
    deriving (Eq, Num, Ord, Show)

instance Enumerable StageID where
    enumerate = [0,1,2,3,4,5,6,7,8,9,10]

type Party p m s = (m,s) -> Dist.T p (m,s)
type SymParty m s = Party SReal m s
type ConcreteParty m s = Party AlgReal m s

data ProtMsg = Play | Open | Ok | Result | Output | Err | Opened
    deriving (Eq, Show, Ord)

instance Enumerable ProtMsg where
    enumerate = [Play, Open, Ok, Result, Output, Err, Opened]

type Msg = (ProtMsg, Bool)

genAdv :: Integer -> Symbolic (SymParty Msg StageID)
genAdv bound = do
    creactions <- (genReactions bound) :: Symbolic [Msg -> SymDist Msg]
    return $ \(m,i) -> do
        let j' = min i (fromInteger (bound - 1))
        case j' of
          Stage j -> do
            m' <- (creactions !! j) m 
            return (m', i+1)

genDetAdv :: Integer -> Symbolic (SymParty Msg StageID)
genDetAdv bound = do
    creactions <- (genDetReactions bound) :: Symbolic [Msg -> SymDist Msg]
    return $ \(m,i) -> do
        let j' = min i (fromInteger (bound - 1))
        case j' of
          Stage j -> do
            m' <- (creactions !! j) m 
            return (m', i+1)

equalParties :: (Eq s, Enumerable s) => SymParty Msg s -> SymParty Msg s -> SBool
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


honestPartyLeftIdeal :: Num p => Bool -> Party p Msg StageID
honestPartyLeftIdeal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, _) -> Dist.certainly $ (msgPlay inp, 1)
      (1, (Result, _)) -> Dist.certainly $ (msgOutput m1, 2)
      _ -> Dist.certainly $ (msgErr, i + 1)

honestPartyRightIdeal :: Num p => Bool -> Party p Msg StageID
honestPartyRightIdeal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, (Ok, _)) -> Dist.certainly $ (msgPlay inp, 1)
      (1, (Result, _)) -> Dist.certainly $ (msgOutput m1, 2)
      _ -> Dist.certainly $ (msgErr, i + 1)

idealFunc :: Num p => Party p Msg (StageID, Bool, Bool)
idealFunc ((m0, m1), (i, p1, p2)) =
    case (i, (m0, m1)) of
      (0, (Play, _)) -> Dist.certainly $ (msgOk, (1, m1, p2))
      (1, (Play, _)) -> Dist.certainly $ (msgResult (m1 <+> p1), (2, p1, m1))
      (2, (Output, _)) -> Dist.certainly $ (msgResult (p1 <+> p2), (3, p1, p2))
      _ -> Dist.certainly (msgErr, (i+1, p1, p2))

runIdeal :: Num p => a -> b -> Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg)
runIdeal a b p1 p2 = do
    (m,s11) <- p1 (msgOk, a)
    (m,sf1) <- idealFunc (m, (0, False, False))
    (m, s21) <- p2 (m, b)
    (m, sf2) <- idealFunc (m, sf1)
    (out1, s12) <- p1 (m, s11)
    (m, _) <- idealFunc (out1, sf2)
    (out2, _) <- p2 (m, s21)
    return (out1, out2)



honestIdealCorrect :: Bool -> Bool -> SBool
honestIdealCorrect i1 i2 = (((msgOutput (i1 <+> i2)), (msgOutput (i1 <+> i2))) ??= (runIdeal 0 0 ((honestPartyLeftIdeal i1) :: SymParty Msg StageID) (honestPartyRightIdeal i2))) .== 1


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

honestPartyLeftReal :: Num p => Bool -> Party p Msg StageID
honestPartyLeftReal inp ((m0, m1), i) =
    case (i, (m0, m1)) of
      (0, (Ok, _)) -> Dist.certainly $ (msgPlay inp, 1)
      (1, (Ok, _)) -> Dist.certainly $ (msgOpen, 2)
      (2, (Opened, _)) -> Dist.certainly (msgOutput (inp <+> m1), 3)
      _ -> Dist.certainly (msgErr, i+1)

honestPartyRightReal :: Num p => Bool -> Party p Msg (StageID, Bool)
honestPartyRightReal inp ((m0, m1), (i, o)) =
    case (i, (m0, m1)) of
      (0, (Ok, _)) -> Dist.certainly $ (msgPlay inp, (1, o))
      (1, (Opened, _)) -> Dist.certainly (msgOpen, (2, m1))
      (2, (Ok, _)) -> Dist.certainly $ (msgOutput (inp <+> o), (4, o))
      _ -> Dist.certainly (msgErr, (i+1, false))

fComm :: Num p => Party p Msg (StageID, Bool)
fComm ((m0, m1), (i,o)) =
    case (i, (m0, m1)) of
      (0, (Play, _)) -> Dist.certainly (msgOk, (1, m1))
      (1, (Open, _)) -> Dist.certainly (msgOpened o, (2, o))
      _ -> Dist.certainly (msgErr, (i+1, o))

runReal :: Num p => a -> b ->  Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg)
runReal inita initb p1 p2 = do
    (m, sa1) <- p1 (msgOk, inita)
    (m, sf11) <- fComm (m, (0, False))
    (m, sb1) <- p2 (m, initb)
    (m, sf21) <- fComm (m, (0, False))
    (m, sa2) <- p1 (m, sa1)
    (m, _) <- fComm (m, sf11)
    (m, sb2) <- p2 (m, sb1)
    (m, _) <- fComm (m, sf21)
    (out1, _) <- p1 (m, sa2)
    (out2, _) <- p2 (msgOk, sb2)
    return (out1, out2)

runIdealFullTrace :: (Show b, Num p) => a -> b -> Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg, [(String, Msg)])
runIdealFullTrace a b p1 p2 = do
    (m1,s11) <- p1 (msgOk, a)
    (m2,sf1) <- idealFunc (m1, (0, False, False))
    (m3, s21) <- p2 (m2, b)
    (m4, sf2) <- idealFunc (m3, sf1)
    (out1, s12) <- p1 (m4, s11)
    (m5, _) <- idealFunc (out1, sf2)
    (out2, _) <- p2 (m5, s21)
    return (out1, out2, [("A", m1), ("F", m2), ("B(" ++ (show b) ++ "," ++ (show m2)++")",m3), ("F",m4), ("A",out1), ("F",m5), ("B(" ++ (show s21) ++ "," ++ (show m5) ++")",out2)])

runRealFullTrace :: (Show b, Num p) => a -> b ->  Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg, [(String, Msg)])
runRealFullTrace inita initb p1 p2 = do
    (m1, sa1) <- p1 (msgOk, inita)
    (m2, sf11) <- fComm (m1, (0, False))
    (m3, sb1) <- p2 (m2, initb)
    (m4, sf21) <- fComm (m3, (0, False))
    (m5, sa2) <- p1 (m4, sa1)
    (m6, _) <- fComm (m5, sf11)
    (m7, sb2) <- p2 (m6, sb1)
    (m8, _) <- fComm (m7, sf21)
    (out1, _) <- p1 (m8, sa2)
    (out2, _) <- p2 (msgOk, sb2)
    return (out1, out2, [("A", m1),("fc1", m2),("B(" ++ (show initb) ++ "," ++ (show m2) ++ ")", m3),("fc2", m4),("A",m5),("fc1",m6),("B(" ++ (show sb1) ++ ", " ++ (show m6)++")",m7),("fc2",m8),("A",out1),("B(" ++ (show sb2) ++ "," ++ (show msgOk)++")",out2)])

runRealWithAdv :: Bool -> ConcreteParty Msg StageID -> ConcreteDist (Msg, Msg, [(String,Msg)])
runRealWithAdv i a = runRealFullTrace 0 0 (honestPartyLeftReal i) a

runIdealWithAdv :: Bool -> ConcreteParty Msg StageID -> ConcreteDist (Msg, Msg, [(String,Msg)])
runIdealWithAdv i a = runIdealFullTrace 0 (0, 0, false) (honestPartyLeftIdeal i) (simulatorRight a)

honestRealCorrect :: Bool -> Bool -> SBool
honestRealCorrect i1 i2 = (((msgOutput (i1 <+> i2)), (msgOutput (i1 <+> i2))) ??= (runReal 0 (0, False) ((honestPartyLeftReal i1) :: SymParty Msg StageID) (honestPartyRightReal i2))) .== 1
     
simulatorRight :: Num p => Party p Msg StageID -> Party p Msg (StageID, StageID, Bool)
simulatorRight adv ((m0, m1), (advs, i, o)) = 
    case (i, (m0, m1)) of
      (0, (Ok, _)) -> do
          ((advm0, advm1), advs') <- adv (msgOk, 0)
          case advm0 of
            Play -> Dist.certainly (msgPlay advm1, (advs', i+1, advm1))
            _ -> Dist.certainly (msgErr, (advs', i+1, o))
      (1, (Result, _)) -> do
          ((advm0, advm1), advs') <- adv (msgOpened (o <+> m1), advs)
          ((m0, m1), advs'') <- adv (msgOk, advs')
          return ((m0,m1), (advs'', i+1, o))
      _ -> Dist.certainly (msgErr, (advs, i+1, o))
                


runRPSSim :: Bool -> Bool -> Symbolic (SymDist (Msg, Msg), SymDist (Msg, Msg), SymParty Msg StageID)
runRPSSim i i2 = do
    a <- genDetAdv 3
    let d1 = (runReal 0 0 (honestPartyLeftReal i) a)
        d2 = (runIdeal 0 (0, 0, false) (honestPartyLeftIdeal i) (simulatorRight a))
    return (d1, d2, a)


rpsSecure :: Bool -> Bool -> Symbolic (SymDist (Msg, Msg), SymDist (Msg, Msg), SBool, SymParty Msg StageID)
rpsSecure i1 i2 = do
    (d1, d2, a) <- runRPSSim i1 i2
    return $ (d1, d2, seqDist d1 d2, a)

           
