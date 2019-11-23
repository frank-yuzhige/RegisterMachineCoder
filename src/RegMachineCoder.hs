module RegMachineCoder where

import Control.Monad
import Data.Array
import Data.Maybe

newtype DPair = DPair {getDPair :: (Integer, Integer)}
  deriving (Eq, Ord)
instance Show DPair where
  show (DPair (a, b)) = "<<" ++ show a ++ ", " ++ show b ++ ">>"

newtype SPair = SPair {getSPair :: (Integer, Integer)}
  deriving (Eq, Ord)
instance Show SPair where
  show (SPair (a, b)) = "<" ++ show a ++ ", " ++ show b ++ ">"

data TwoPow = TP {get2Pow :: Integer, getFactor :: Integer}
instance Eq TwoPow where
  (TP p1 b1) == (TP p2 b2) = p1' == p2' && b1' == b2'
    where
      TP p1' b1' = neutralizeTP p1 b1
      TP p2' b2' = neutralizeTP p2 b2
instance Show TwoPow where
  show (TP p b) = "2^" ++ show p ++ " * " ++ show b
instance Num TwoPow where
  (TP p1 b1) + (TP p2 b2) = neutralizeTP p b
    where
      p = p1 `min` p2
      diff = p1 - p2
      b = if diff < 0 then b1 + 2 ^ (abs diff) * b2
                      else b2 + 2 ^ (abs diff) * b1
  (TP p1 b1) * (TP p2 b2) = neutralizeTP p b
    where
      p = p1 + p2
      b = b1 * b2
  abs (TP p b) = TP p (abs b)
  signum (TP _ b) = TP 0 (signum b)
  fromInteger = toTwoPow
  negate (TP p b) = TP p (negate b)

type Reg = Integer
type Line = Integer
type Program = [Instruction]
data Instruction = Inc  Line Reg Line
                 | Dec  Line Reg Line Line
                 | Halt Line
                 deriving (Eq)

instance Show Instruction where
  show (Halt c) = "[L" ++ show c ++ "]: HALT\n"
  show (Inc c l t) = "[L" ++ show c ++ "]: R" ++ show l ++ "+ => L" ++ show t ++ "\n"
  show (Dec c l t1 t2) = "[L" ++ show c ++ "]: R" ++ show l ++ "- => L" ++ show t1 ++ ",L" ++ show t2 ++ "\n"

getReg :: Instruction -> Maybe Reg
getReg (Halt _) = Nothing
getReg (Inc _ r _) = Just r
getReg (Dec _ r _ _) = Just r

getLineCode :: Instruction -> Line
getLineCode (Halt l) = l
getLineCode (Inc l _ _) = l
getLineCode (Dec l _ _ _) = l 

getTargets :: Instruction -> [Line]
getTargets (Halt _) = []
getTargets (Inc _ _ t) = [t]
getTargets (Dec _ _ t1 t2) = [t1, t2]

data RegMachine = RM { getProgramArray :: Array Line Instruction
                     , getState :: Array Reg Integer
                     , getPC :: Line
                     }
                deriving (Show)

data ResultType = ErroneousHalt | NormalHalt Line
                deriving (Eq, Show)

appendConfig :: [Integer] -> Result -> Result
appendConfig xs (Result xss t) = Result (xs : xss) t 

data Result = Result [[Integer]] ResultType
            deriving (Eq, Show)

evalResult :: Result -> String
evalResult (Result cs t) = 
  "The register machine starts with config: " ++ show (head cs) ++ "\n" ++
  "It finished with " ++ show t ++ "\n" ++
  "It's final state is: " ++ show (last cs) ++ "\n" ++
  "The full computation is: " ++ show cs
setupRM :: Program -> [Integer] -> Maybe RegMachine
setupRM _ [] = Nothing
setupRM ps (pc : ss) 
  | not $ all (`elem` [0 .. regCount]) lhsRegs = Nothing
  | otherwise = Just $ RM (array (0, insCount - 1) ps') (array (0, regCount - 1) $ zip [0..] ss) pc 
  where
    insCount = fromIntegral $ length ps
    regCount = fromIntegral $ length ss
    lhsRegs = mapMaybe getReg ps
    ps' = zip (map getLineCode ps) ps

runRM1Step :: RegMachine -> Either Result RegMachine
runRM1Step (RM ps state pc)
  | pc > u    = Left $ Result [pc : elems state] ErroneousHalt
  | otherwise = case ps ! pc of
      Halt l        -> Left $ Result [l : elems state] (NormalHalt l)
      Inc _ r next  -> Right $ RM ps (state // [(r, (state ! r) + 1)]) next
      Dec _ r n1 n2 -> let rVal = state ! r 
                       in Right $ if rVal == 0 then RM ps state n2
                                               else RM ps (state // [(r, rVal - 1)]) n1
  where
    (l, u) = bounds ps

runRM :: RegMachine -> Result
runRM rm = case runRM1Step rm of
    Left result -> result
    Right rm'   -> appendConfig (getRMConfig rm) $ runRM rm'

getRMConfig :: RegMachine -> [Integer]
getRMConfig (RM _ state pc) = pc : elems state

fromTwoPow :: TwoPow -> Integer
fromTwoPow (TP p b) = 2 ^ p * b

toTwoPow :: Integer -> TwoPow
toTwoPow 0 = TP 0 0
toTwoPow n = TP x y
  where
    x = getMaxTwoPowFactor n
    y = n `quot` (2 ^ x)

neutralizeTP :: Integer -> Integer -> TwoPow
neutralizeTP p b
  | b == 0          = TP 0 0
  | r == 0 && q > 0 = neutralizeTP  (p + 1) q
  | otherwise       = TP p b
  where
    (q, r) = b `quotRem` 2

fromDPair :: DPair -> TwoPow
fromDPair (DPair (x, y)) = TP x (2 * y + 1)

toDPair :: TwoPow -> DPair
toDPair (TP p b) = DPair (p, b `quot` 2)

encodeDPair :: Integer -> TwoPow -> TwoPow
encodeDPair x y = fromDPair $ DPair (x, fromTwoPow y)

fromSPair :: SPair -> Integer
fromSPair (SPair (x, y)) = 2 ^ x * (2 * y + 1) - 1

toSPair :: Integer -> SPair
toSPair n = SPair (x, y)
  where
    DPair (x, y) = toDPair $ toTwoPow (n + 1)

encodeSPair :: Integer -> Integer -> Integer
encodeSPair x y = fromSPair $ SPair (x, y)

getMaxTwoPowFactor :: Integer -> Integer
getMaxTwoPowFactor x = head (dropWhile ((== 0) . (x `mod`) . (2 ^)) [0..]) - 1

encodeList :: [Integer] -> TwoPow
encodeList = foldr encodeDPair (TP 0 0)

decodeList :: TwoPow -> [Integer]
decodeList (TP p b)
  | b == 0    = []
  | otherwise = p : decodeList (toTwoPow q)
  where
    (q, _) = b `quotRem` 2

decodeInstruction :: Integer -> Integer -> Instruction
decodeInstruction 0 i = Halt i
decodeInstruction c i
  | even x    = Inc i (x `div` 2) y
  | otherwise = Dec i (x `div` 2) j k
    where
      DPair (x, y) = toDPair $ toTwoPow c
      SPair (j, k) = toSPair y

decodeProgram :: TwoPow -> Program
decodeProgram (TP p b) = decodeProgramFromList (decodeList $ neutralizeTP p b)

decodeProgramFromList :: [Integer] -> Program
decodeProgramFromList = flip (zipWith decodeInstruction) [0..]

encodeInstruction :: Instruction -> TwoPow
encodeInstruction (Halt _) = TP 0 0
encodeInstruction (Inc _ i l) = fromDPair (DPair (2 * i, l))
encodeInstruction (Dec _ i j k) = fromDPair (DPair (2 * i + 1, fromSPair (SPair (j, k))))

encodeProgram :: Program -> TwoPow
encodeProgram = encodeList . map (fromTwoPow . encodeInstruction)

-- decodeProgramWithSteps :: IO ()
-- decodeProgramWithSteps = do
--   putStrLn "2^m * n, please input m:"
--   m <- (read <$> getLine) :: IO Integer
--   putStrLn "please input n:"
--   n <- (read <$> getLine) :: IO Integer
--   let tp = neutralizeTP m n
--   putStrLn $ "Your original code is: " ++ show tp
--   let list = decodeList tp
--   putStrLn $ "Decoded list is: " ++ show list
--   mapM_ list

ps = decodeProgramFromList [184, 0, 1144, 4600, 0 ,1]
rm = fromJust $ setupRM ps [0, 0, 7]