import Providers
import Data.HVect

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

-- only one kind of experiment here
experiment : (Bool, Nat, Nat) -> IO (Provider Type)
experiment inp@(o, a1, a2) = do
  out <- return $ if o then a1 + a2 else (if lte a2 a1 then a1 - a2 else a1 * a2)
  return (Provide (blackbox inp = out))

-- beginning to poke the box
%provide (t00 : Type) with (experiment (True, Z, Z))
%provide (t01 : Type) with (experiment (True, Z, 1))
%provide (t10 : Type) with (experiment (True, 1, Z))
%provide (t11 : Type) with (experiment (True, 1, 1))
%provide (f00 : Type) with (experiment (False, Z, Z))
%provide (f01 : Type) with (experiment (False, Z, 1))
%provide (f10 : Type) with (experiment (False, 1, Z))
%provide (f11 : Type) with (experiment (False, 1, 1))

initialTests : MTL 8
initialTests = [t00, t01, t10, t11, f00, f01, f10, f11]
-- blackbox (True, 0, 0) = 0
-- blackbox (True, 0, 1) = 1
-- blackbox (True, 1, 0) = 1
-- blackbox (True, 1, 1) = 2
-- blackbox (False, 0, 0) = 0
-- blackbox (False, 0, 1) = 0
-- blackbox (False, 1, 0) = 1
-- blackbox (False, 1, 1) = 0

-- the first guess
tPlusFMinus : {ib: Bool} -> {in1, in2, o: Nat} -> (blackbox (ib, in1, in2) = o) -> Type
tPlusFMinus {ib} {in1} {in2} {o} ob = if ib then o = in1 + in2 else o = in1 - in2

-- confirmTPlusFMinus : HVect (confirm tPlusFMinus initialTests)
-- confirmTPlusFMinus = [\x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl, \x => Refl]

%provide (t42_23 : Type) with (experiment (True, 42, 23))
%provide (t23_42 : Type) with (experiment (True, 23, 42))
%provide (f42_23 : Type) with (experiment (False, 42, 23))
%provide (f23_42 : Type) with (experiment (False, 23, 42))

furtherTests : MTL 4
furtherTests = [t42_23, t23_42, f42_23, f23_42]
-- blackbox (True, 42, 23) = 65
-- blackbox (True, 23, 42) = 65
-- blackbox (False, 42, 23) = 19
-- blackbox (False, 23, 42) = 966

-- confirmTPlusFMinus2 : HVect (confirm tPlusFMinus furtherTests)
-- confirmTPlusFMinus2 = ?mv

-- uh oh, 966 = 0!

refuteTPlusFMinus2 : f23_42 -> HVect (confirm tPlusFMinus furtherTests) -> Void
refuteTPlusFMinus2 f [_,_,_,d] = uninhabited (sym (d f))

-- is it multiplication? why it happened?

%provide (f3_5 : Type) with (experiment (False, 3, 5))
%provide (f5_3 : Type) with (experiment (False, 5, 3))
%provide (f7_13 : Type) with (experiment (False, 7, 13))
%provide (f13_7 : Type) with (experiment (False, 13, 7))

moreTests : MTL 4
moreTests = [f3_5, f5_3, f7_13, f13_7]
-- blackbox (False, 3, 5) = 15
-- blackbox (False, 5, 3) = 2
-- blackbox (False, 7, 13) = 91
-- blackbox (False, 13, 7) = 6
 
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

