module Issue6962Parser where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- The LHS bridge reuses all binder forms, including hidden binders inside
-- parentheses followed by a named hidden binder.
parameters ({A} : Set) {C = B : Set} (x : A) (_ : B) : A
parameters = x

parameters-test : parameters {Nat} {C = Nat} 2 3 ≡ 2
parameters-test = refl

namedInstance {{value = n : Nat}} : Nat
namedInstance = n

namedInstance-test : namedInstance {{value = 4}} ≡ 4
namedInstance-test = refl

-- Without a colon inside the braces, named arguments on a clause LHS
-- retain their ordinary interpretation.
ordinary : {B : Set} → B → {{value : Nat}} → B
ordinary {B = A} x {{value = n}} = x

ordinary-test : ordinary {B = Nat} 2 {{value = 3}} ≡ 2
ordinary-test = refl

-- Nested expressions continue to use the ordinary expression grammar.
-- In particular, telescopes still require an arrow, and lambdas can mix
-- typed and untyped binders with external/internal argument names.
lambda : Nat → {B : Set} → B → B
lambda = λ n {B = A} (x : A) → x

lambda-test : lambda 2 {B = Nat} 3 ≡ 3
lambda-test = refl

telescope : ({A} : Set) (x : A) → A
telescope x = x

telescope-test : telescope {Nat} 3 ≡ 3
telescope-test = refl
