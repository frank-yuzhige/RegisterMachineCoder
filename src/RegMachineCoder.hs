module RegMachineCoder where

import Control.Monad

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
data Instruction = Inc  {getLineCode :: Line, getLHS :: Reg, getT :: Line}
                 | Dec  {getLineCode :: Line, getLHS :: Reg, getT1 :: Line, getT2 :: Line}
                 | HALT {getLineCode :: Line}
                 deriving (Eq)

instance Show Instruction where
  show (HALT c) = "[L" ++ show c ++ "]: HALT\n"
  show (Inc c l t) = "[L" ++ show c ++ "]: R" ++ show l ++ "+ => L" ++ show t ++ "\n"
  show (Dec c l t1 t2) = "[L" ++ show c ++ "]: R" ++ show l ++ "- => L" ++ show t1 ++ ",L" ++ show t2 ++ "\n"

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
decodeInstruction 0 i = HALT i
decodeInstruction c i
  | even x    = Inc i (x `div` 2) y
  | otherwise = Dec i (x `div` 2) j k
    where
      DPair (x, y) = toDPair $ toTwoPow c
      SPair (j, k) = toSPair y

decodeProgram :: TwoPow -> Program
decodeProgram (TP p b) = zipWith decodeInstruction (decodeList $ neutralizeTP p b) [0..]

encodeInstruction :: Instruction -> TwoPow
encodeInstruction (HALT _) = TP 0 0
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