import Providers
import Data.HVect
import Data.Fin

%default total
%language TypeProviders

-- Playing with reasoning about black boxes here. The goal is not to
-- reconstruct their algorithms (which won't be possible in many
-- cases), but to experiment, make statements about their behaviour,
-- confirm or refute those, and reason using those statements as
-- premises.

-- Confirmations are commented out, because they take a bit too much
-- time and memory to typecheck, but they are fine

-- Not using Dec here, mostly because of laziness, but in some cases
-- it might be much more convenient. Also would be nice to add type
-- aliases for common things.


postulate blackbox : (Bool, Nat, Nat) -> Nat

-- there should be a nicer way to do this, without an additonal type
data MTL : Nat -> Type where
  Nil : MTL Z
  (::) : {ib:Bool} -> {in1, in2, out: Nat} -> (t:Type) ->
       {auto eq: t = (blackbox (ib, in1, in2) = out)} -> {n: Nat} -> MTL n -> MTL (S n)

(++) : MTL m -> MTL n -> MTL (m + n)
(++) [] ys = ys
(++) ((::) x {eq} xs) ys = (::) x {eq} $ xs ++ ys

index : Fin n -> MTL n -> Type
index FZ     (x::xs) = x
index (FS k) (x::xs) = index k xs
index FZ     [] impossible

-- simply turns (f: bb -> Type) into ((x:bb) -> f x)
h : ({ib: Bool} -> {in1, in2, o: Nat} -> blackbox (ib, in1, in2) = o -> Type) -> Type
h f = {ib: Bool} -> {in1, in2, o: Nat} -> (x:(blackbox (ib, in1, in2) = o)) -> f x

-- applies a model to an observation
mt : {ib:Bool} -> {in1, in2, out: Nat} ->
   ({ib: Bool} -> {in1, in2, o: Nat} -> (blackbox (ib, in1, in2) = o) -> Type) ->
   (t:Type) -> {auto eq: t = (blackbox (ib, in1, in2) = out)} -> Type
mt {ib} {in1} {in2} {out} f t = (x:(blackbox (ib, in1, in2) = out)) -> f x

-- same, but for a bunch of observations
confirm : ({ib: Bool} -> {in1, in2, o: Nat} -> (blackbox (ib, in1, in2) = o) -> Type) -> MTL n -> Vect n Type
confirm f [] = []
confirm f ((::) x xs {eq}) = mt f x {eq} :: confirm f xs



-- only one kind of experiment here, in two versions: for single and
-- multiple tests
experiment : (Bool, Nat, Nat) -> IO (Provider Type)
experiment inp@(o, a1, a2) = do
  out <- return $ if o then a1 + a2 else (if lte a2 a1 then a1 - a2 else a1 * a2)
  return (Provide (blackbox inp = out))

experiment' : Vect n (Bool, Nat, Nat) -> IO (MTL n)
experiment' [] = return []
experiment' (inp@(o, a1, a2)::xs) = do
  out <- return $ if o then a1 + a2 else (if lte a2 a1 then a1 - a2 else a1 * a2)
  next <- experiment' xs
  return $ (blackbox inp = out) :: next

experimentV : Vect n (Bool, Nat, Nat) -> IO (Provider (MTL n))
experimentV v = do
  types <- experiment' v
  return (Provide types)


-- beginning to poke the box
%provide (initialTests : MTL 8) with (experimentV [
         (True, 0, 0),  -- 0
         (True, 0, 1),  -- 1
         (True, 1, 0),  -- 1
         (True, 1, 1),  -- 2
         (False, 0, 0), -- 0
         (False, 0, 1), -- 0
         (False, 1, 0), -- 1
         (False, 1, 1)  -- 0
         ])

-- the first guess
tPlusFMinus : {ib: Bool} -> {in1, in2, o: Nat} -> (blackbox (ib, in1, in2) = o) -> Type
tPlusFMinus {ib} {in1} {in2} {o} ob = if ib then o = in1 + in2 else o = in1 - in2

-- confirmTPlusFMinus : HVect (confirm tPlusFMinus initialTests)
-- confirmTPlusFMinus = [\x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl]

%provide (furtherTests : MTL 4) with (experimentV [
         (True, 42, 23),  -- 65
         (True, 23, 42),  -- 65
         (False, 42, 23), -- 19
         (False, 23, 42)  -- 966
         ])

-- confirmTPlusFMinus2 : HVect (confirm tPlusFMinus furtherTests)
-- confirmTPlusFMinus2 = ?mv -- uh oh, 966 = 0!

refuteTPlusFMinus2 : index 3 furtherTests -> HVect (confirm tPlusFMinus furtherTests) -> Void
refuteTPlusFMinus2 f [_,_,_,d] = uninhabited (sym (d f))

-- is it multiplication? why it happened?

%provide (moreTests : MTL 4) with (experimentV [
         (False, 3, 5),  -- 15
         (False, 5, 3),  -- 2
         (False, 7, 13), -- 91
         (False, 13, 7)  -- 6
         ])
 
-- ok, it happens when the first Nat is lower

tPlusFMinusMult : {ib: Bool} -> {in1, in2, o: Nat} -> (blackbox (ib, in1, in2) = o) -> Type
tPlusFMinusMult {ib} {in1} {in2} {o} ob =
  o = if ib then in1 + in2 else (if lte in2 in1 then in1 - in2 else in1 * in2)

-- confirmTPlusFMinusMult : HVect (confirm tPlusFMinusMult $ initialTests ++ furtherTests ++ moreTests)
-- confirmTPlusFMinusMult = confirmTPlusFMinus ++ [\x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl]

-- now we could reason using this model

tCommutative : {in1, in2, o1, o2: Nat} ->
             -- for any two black box runs with their Nat arguments swapped, and Bool arg = True…
             (blackbox (True, in1, in2) = o1) -> (blackbox (True, in2, in1) = o2) ->
             -- according to tPlusFMinusMult…
             (h tPlusFMinusMult) ->
             -- outputs are equal
             o1 = o2
tCommutative {in1} {in2} {o1} {o2} b1 b2 f with (f b1, f b2)
  | (r1, r2) = rewrite r1 in rewrite r2 in plusCommutative in1 in2

