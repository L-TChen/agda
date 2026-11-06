{-# OPTIONS --erasure #-}

module Issue6962 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

typedVisible (A : Set) : A -> A
typedVisible x = x

typedVisible-test : typedVisible Nat zero ≡ zero
typedVisible-test = refl

hiddenParam {A : Set} (x : A) : A
hiddenParam = x

hiddenParam-test : hiddenParam {Nat} zero ≡ zero
hiddenParam-test = refl

namedHiddenLHS : {A : Set} -> A -> A
namedHiddenLHS {A = A} x = x

namedHiddenLHS-test : namedHiddenLHS {Nat} zero ≡ zero
namedHiddenLHS-test = refl

compose
  {A B C : Set}
  (f : B -> C)
  (g : A -> B)
  : A -> C
compose x = f (g x)

compose-test : compose suc suc zero ≡ suc (suc zero)
compose-test = refl

whereParam {A : Set} (x : A) : A
whereParam = helper
  where
    helper : A
    helper = x

whereParam-test : whereParam zero ≡ zero
whereParam-test = refl

letParam : Nat
letParam =
  let
    go {A : Set} : A -> A
    go x = x
  in go zero

letParam-test : letParam ≡ zero
letParam-test = refl

typedAfterUntyped {a} (A : Set a) : A -> A
typedAfterUntyped x = x

typedAfterUntyped-test : typedAfterUntyped Nat zero ≡ zero
typedAfterUntyped-test = refl

record FieldAmbiguity : Set where
  field
    first {second} third : Nat -> Nat

fieldAmbiguity : FieldAmbiguity
fieldAmbiguity = record
  { first  = \ x -> x
  ; second = \ x -> suc x
  ; third  = \ x -> suc (suc x)
  }

first-test : FieldAmbiguity.first fieldAmbiguity zero ≡ zero
first-test = refl

second-test : FieldAmbiguity.second fieldAmbiguity zero ≡ suc zero
second-test = refl

third-test : FieldAmbiguity.third fieldAmbiguity zero ≡ suc (suc zero)
third-test = refl

-- Parameters are ordinary arguments, including in recursive calls.
recursive (A : Set) : Nat -> Nat
recursive zero = zero
recursive (suc n) = recursive Nat n

recursive-test : recursive (Nat -> Nat) 4 ≡ zero
recursive-test = refl

hiddenRecursive {A : Set} : Nat -> Nat
hiddenRecursive zero = zero
hiddenRecursive (suc n) = hiddenRecursive {Nat} n

hiddenRecursive-test : hiddenRecursive {Nat -> Nat} 4 ≡ zero
hiddenRecursive-test = refl

-- Preserve the external argument name independently of its local name.
renamed {B = A : Set} (x : A) : A
renamed = x

renamed-test : renamed {B = Nat} zero ≡ zero
renamed-test = refl

instanceParam {{n : Nat}} : Nat
instanceParam = n

instance-test : instanceParam {{3}} ≡ 3
instance-test = refl

erased (@0 A : Set) : Nat -> Nat
erased n = n

erased-test : erased Nat 2 ≡ 2
erased-test = refl

irrelevant .(n : Nat) : Nat
irrelevant = zero

irrelevant-test : irrelevant 3 ≡ zero
irrelevant-test = refl

anonymous (_ : Nat) : Nat
anonymous = zero

anonymous-test : anonymous 3 ≡ zero
anonymous-test = refl

-- Explicit untyped binders after a typed one are inferred from the result.
untyped (A : Set) x : A
untyped = x

untyped-test : untyped Nat zero ≡ zero
untyped-test = refl

module UnderModule (A : Set) where
  local (x : A) : A
  local = x

module-test : UnderModule.local Nat zero ≡ zero
module-test = refl

mutual
  even (A : Set) : Nat -> Nat
  even zero = zero
  even (suc n) = odd Nat n

  odd (A : Set) : Nat -> Nat
  odd zero = zero
  odd (suc n) = even A n

mutual-test : even (Nat -> Nat) 5 ≡ zero
mutual-test = refl

interleaved mutual
  first (A : Set) : Nat -> Nat
  second (A : Set) : Nat -> Nat
  first zero = zero
  second zero = zero
  first (suc n) = second Nat n
  second (suc n) = first A n

interleaved-test : first Nat 5 ≡ zero
interleaved-test = refl

withParam (n : Nat) : Nat -> Nat
withParam m with m
... | zero = n
... | suc k = withParam (suc n) k

with-test : withParam 2 3 ≡ 5
with-test = refl

rewriteParam (n : Nat) : n ≡ n -> Nat
rewriteParam eq rewrite eq = n

rewrite-test : rewriteParam 3 refl ≡ 3
rewrite-test = refl

record Box (A : Set) : Set where
  field value : A

boxed {A : Set} (x : A) : Box A
Box.value boxed = x

copattern-test : Box.value (boxed zero) ≡ zero
copattern-test = refl

_pick_ (A : Set) : A -> A -> A
x pick y = x

infix-test : _pick_ Nat 2 3 ≡ 2
infix-test = refl

-- Generalisation in the result remains inside the parameter prefix.
variable B : Set

generalizedResult (A : Set) : B -> B
generalizedResult x = x

generalized-test : generalizedResult Nat zero ≡ zero
generalized-test = refl

-- Existing multiple signatures still declare separate functions.
ordinary₁ ordinary₂ : Nat
ordinary₁ = zero
ordinary₂ = suc zero

renamedUntyped {B = A} (x : A) : A ≡ Nat -> A
renamedUntyped eq = x

renamedUntyped-test : renamedUntyped {B = Nat} 2 refl ≡ 2
renamedUntyped-test = refl

grouped (A B : Set) (x : A) (_ _ : B) : A
grouped = x

grouped-test : grouped Nat Nat 1 2 3 ≡ 1
grouped-test = refl

nested (A : Set) (x : A) : A
nested = inner x
  where
  inner (y : A) : A
  inner = let local (z : A) : A
              local = z
          in local y

nested-test : nested Nat 4 ≡ 4
nested-test = refl

module WithModule (p : Nat) where
  withBoth (n : Nat) : Nat -> Nat
  withBoth m with m
  ... | zero = p + n
  ... | suc k with k
  ...   | zero = n
  ...   | suc l = withBoth (suc n) l

withBoth-test : WithModule.withBoth 2 3 4 ≡ 7
withBoth-test = refl

-- Retrying a definition with an initially unknown argument type must retain
-- the parameter telescope and its body scope.
mutual
  postponed (n : Nat) : _ -> Nat
  postponed zero = n
  postponed (suc m) = postponed (suc n) m

  postponed-type : (n : Nat) -> Nat -> Nat
  postponed-type n = postponed n

postponed-test : postponed 2 3 ≡ 5
postponed-test = refl
