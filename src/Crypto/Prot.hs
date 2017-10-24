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

data Msg = Play Bool | Open | Ok | Result Bool | Output Bool | Err | Opened Bool
    deriving (Show, Ord, Eq)

instance Enumerable Msg where
    enumerate = [Open, Ok, Err] ++ (map Play enumerate) ++ (map Result enumerate) ++ (map Output enumerate) ++ (map Opened enumerate)

{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to B
   B: output Ok or Err to A
   F: send result to A, unless err, then send err to a
   A : output result
   B : output result
-}


honestPartyLeftIdeal :: Num p => Bool -> Party p Msg StageID
honestPartyLeftIdeal inp (m, i) =
    case (i, m) of
      (0, _) -> Dist.certainly $ (Play inp, 1)
      (1, (Result m1)) -> Dist.certainly $ (Output m1, 2)
      _ -> Dist.certainly $ (Err, i + 1)

honestPartyRightIdeal :: Num p => Bool -> Party p Msg (StageID, Bool)
honestPartyRightIdeal inp (m, (i, s)) =
    case (i, m) of
      (0, (Ok)) -> Dist.certainly $ (Play inp, (1, s))
      (1, Result m1) -> return (Ok, (2, m1))
      (2, Ok) -> Dist.certainly $ (Output s, (2, s))
      _ -> Dist.certainly $ (Err, (i + 1, s))

idealFunc :: Num p => Party p Msg (StageID, Bool, Bool)
idealFunc (m, (i, p1, p2)) =
    case (i, m) of
      (0, (Play m1)) -> Dist.certainly $ (Ok, (1, m1, p2))
      (1, (Play m1)) -> Dist.certainly $ (Result (m1 <+> p1), (2, p1, m1))
      (2, Ok) -> Dist.certainly $ (Result (p1 <+> p2), (3, p1, p2))
      _ -> Dist.certainly (Err, (i+1, p1, p2))

runIdeal :: Num p => a -> b -> Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg)
runIdeal a b p1 p2 = do
    (m,s11) <- p1 (Ok, a)
    (m,sf1) <- idealFunc (m, (0, False, False))
    (m, s21) <- p2 (m, b)
    (m, sf2) <- idealFunc (m, sf1)
    (m, s22) <- p2 (m, s21)
    (m, _) <- idealFunc (m, sf2)
    (out1, _) <- p1 (m, s11)
    (out2, _) <- p2 (Ok, s22)
    return (out1, out2)



honestIdealCorrect :: Bool -> Bool -> SBool
honestIdealCorrect i1 i2 = (((Output (i1 <+> i2)), (Output (i1 <+> i2))) ??= (runIdeal 0 (0, false) ((honestPartyLeftIdeal i1) :: SymParty Msg StageID) (honestPartyRightIdeal i2))) .== 1


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
honestPartyLeftReal inp (m, i) =
    case (i, m) of
      (0, (Ok)) -> Dist.certainly $ (Play inp, 1)
      (1, (Ok)) -> Dist.certainly $ (Open, 2)
      (2, (Opened m1)) -> Dist.certainly (Output (inp <+> m1), 3)
      _ -> Dist.certainly (Err, i+1)

honestPartyRightReal :: Num p => Bool -> Party p Msg (StageID, Bool)
honestPartyRightReal inp (m, (i, o)) =
    case (i, m) of
      (0, (Ok)) -> Dist.certainly $ (Play inp, (1, o))
      (1, (Opened m1)) -> Dist.certainly (Open, (2, m1))
      (2, (Ok)) -> Dist.certainly $ (Output (inp <+> o), (4, o))
      _ -> Dist.certainly (Err, (i+1, false))

fComm :: Num p => Party p Msg (StageID, Maybe Bool)
fComm (m, (i,o)) =
    case (i, m) of
      (0, (Play m1)) -> Dist.certainly (Ok, (1, Just m1))
      (1, (Open)) | Just b <- o -> Dist.certainly (Opened b, (2, o))
      _ -> Dist.certainly (Err, (i+1, o))

runReal :: Num p => a -> b ->  Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg)
runReal inita initb p1 p2 = do
    (m, sa1) <- p1 (Ok, inita)
    (m, sf11) <- fComm (m, (0, Nothing))
    (m, sb1) <- p2 (m, initb)
    (m, sf21) <- fComm (m, (0, Nothing))
    (m, sa2) <- p1 (m, sa1)
    (m, _) <- fComm (m, sf11)
    (m, sb2) <- p2 (m, sb1)
    (m, _) <- fComm (m, sf21)
    (out1, _) <- p1 (m, sa2)
    (out2, _) <- p2 (Ok, sb2)
    return (out1, out2)

runIdealFullTrace :: (Show b,Num p) => a -> b -> Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg, [(String,Msg)])
runIdealFullTrace a b p1 p2 = do
    (m1,s11) <- p1 (Ok, a)
    (m2,sf1) <- idealFunc (m1, (0, False, False))
    (m3, s21) <- p2 (m2, b)
    (m4, sf2) <- idealFunc (m3, sf1)
    (m5, s22) <- p2 (m4, s21)
    (m6, _) <- idealFunc (m5, sf2)
    (out1, _) <- p1 (m6, s11)
    (out2, _) <- p2 (Ok, s22)
    return (out1, out2, [("A", m1),("F", m2),("B("++(show b)++")", m3),("F", m4),("B("++(show s21)++")",m5),("F",m6),("A",out1),("B(" ++ (show s22) ++")",out2)])

runRealFullTrace :: (Show b, Num p) => a -> b ->  Party p Msg a -> Party p Msg b -> Dist.T p (Msg, Msg, [(String, Msg)])
runRealFullTrace inita initb p1 p2 = do
    (m1, sa1) <- p1 (Ok, inita)
    (m2, sf11) <- fComm (m1, (0, Nothing))
    (m3, sb1) <- p2 (m2, initb)
    (m4, sf21) <- fComm (m3, (0, Nothing))
    (m5, sa2) <- p1 (m4, sa1)
    (m6, _) <- fComm (m5, sf11)
    (m7, sb2) <- p2 (m6, sb1)
    (m8, _) <- fComm (m7, sf21)
    (out1, _) <- p1 (m8, sa2)
    (out2, _) <- p2 (Ok, sb2)
    return (out1, out2, [("A", m1),("fc1", m2),("B(" ++ (show initb) ++ ")", m3),("fc2", m4),("A",m5),("fc1",m6),("B(" ++ (show sb1) ++ ")",m7),("fc2",m8),("A",out1),("B(" ++ (show sb2),out2)])

runRealWithAdv :: Bool -> ConcreteParty Msg StageID -> ConcreteDist (Msg, Msg, [(String,Msg)])
runRealWithAdv i a = runRealFullTrace 0 0 (honestPartyLeftReal i) a

runIdealWithAdv :: Bool -> ConcreteParty Msg StageID -> ConcreteDist (Msg, Msg, [(String, Msg)])
runIdealWithAdv i a = runIdealFullTrace 0 (0, 0, false) (honestPartyLeftIdeal i) (simulatorRight a)

honestRealCorrect :: Bool -> Bool -> SBool
honestRealCorrect i1 i2 = (((Output (i1 <+> i2)), (Output (i1 <+> i2))) ??= (runReal 0 (0, False) ((honestPartyLeftReal i1) :: SymParty Msg StageID) (honestPartyRightReal i2))) .== 1
     
{-
   A: activated, send play b to F
   F: send ok to B
   B: send play b' to F
   F: send result (b xor b') to B
   B: output Ok or Err to A
   F: send result to A, unless err, then send err to a
   A : output result
   B : output result
-}

simulatorRight :: Num p => Party p Msg StageID -> Party p Msg (StageID, StageID, Bool)
simulatorRight adv (m, (advs, i, o)) = 
    case (i, m) of
      (0, Ok) -> do
          (advm, advs') <- adv (Ok, 0)
          case advm  of
            Play advm1 -> Dist.certainly (Play advm1, (advs', i+1, advm1))
            _ -> Dist.certainly (Err, (advs', i+1, o))
      (1, (Result b)) -> do
          (m', advs') <- adv (Opened (o <+> b), i)
          case m' of
            Open -> Dist.certainly (Ok, (advs', i+1, o))
            _ -> Dist.certainly (Err, (advs', i+1, o))
      (2, Ok) -> do
          (m'', advs'') <- adv (Ok, i)
          return (m'', (advs'', i+1, o))
      _ -> Dist.certainly (Err, (advs, i+1, o))
                


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

           
