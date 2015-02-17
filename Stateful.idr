import Providers
-- import Data.HVect
-- import Data.Fin


%default total
%language TypeProviders

-- Enumerating observations, in order to be able to reason about
-- sequences, and to avoid introducing contradictory types.

-- Assumptions could depend on a few observations at once, so
-- something like lists of observations should be used instead of
-- single ones, and checks against permutations then, perhaps.

-- #, input, output
postulate blackbox : Integer -> Integer -> Integer


partial parseDigit : Char -> Integer
parseDigit '0' = 0
parseDigit '1' = 1
parseDigit '2' = 2
parseDigit '3' = 3
parseDigit '4' = 4
parseDigit '5' = 5
parseDigit '6' = 6
parseDigit '7' = 7
parseDigit '8' = 8
parseDigit '9' = 9

partial parseInt : String -> Integer
parseInt s = foldl (\x,y => 10*x + parseDigit y) 0 (unpack s)

partial parseState : String -> (Integer, Integer)
parseState s = case (words s) of
  [w1, w2] => (parseInt w1, parseInt w2)

partial experiment : Integer -> IO (Provider Type)
experiment inp = do
  val <- readFile "/tmp/black-box-test"
  (n, out) <- return $ parseState val
  fh <- openFile "/tmp/black-box-test" Write
  fwrite fh $ show (n + 1) ++ " " ++ show (out + inp)
  closeFile fh
  return (Provide (blackbox (n + 1) inp = (out + inp)))

%provide (first : Type) with (experiment 2)
%provide (second : Type) with (experiment 4)
%provide (third : Type) with (experiment 1)

alwaysIncreases' : blackbox num1 inp1 = out1 -> blackbox num2 inp2 = out2 -> Type
alwaysIncreases' {num1} {num2} {out1} {out2} b1 b2 = (if num1 <= num2 then out1 <= out2 else out2 <= out1) = True

increasesByInput' : blackbox num1 inp1 = out1 -> blackbox num2 inp2 = out2 -> Type
increasesByInput' {num1} {num2} {inp1} {inp2} {out1} {out2} b1 b2 = case (num1 == num2 - 1) of
  True => out2 = out1 + inp2
  False => case (num1 == num2 + 1) of
    True => out1 = out2 + inp1
    False => Unit

c1IncreasesByInput' : (b1:first) -> (b2:second) -> increasesByInput' b1 b2
c1IncreasesByInput' b1 b2 = Refl

c2IncreasesByInput' : (b1:first) -> (b2:second) -> increasesByInput' b2 b1
c2IncreasesByInput' b1 b2 = Refl

c3IncreasesByInput' : (b1:first) -> (b3:third) -> increasesByInput' b1 b3
c3IncreasesByInput' b1 b3 = MkUnit

