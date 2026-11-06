module Issue6962Split where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- Reload the clauses emitted by test/Interaction/Issue6962, filling each
-- hole with a header parameter that must remain in scope.
visible (n : Nat) : Nat -> Nat
visible zero = n
visible (suc m) = n

hidden {n : Nat} : Nat -> Nat
hidden zero = n
hidden (suc m) = n

withParam (n : Nat) : Nat -> Nat -> Nat
withParam m k with m
withParam m zero | zero = n
withParam m (suc k) | zero = n
withParam m k | suc j = n

module M (p : Nat) where
  local (n : Nat) : Nat -> Nat
  local zero = n
  local (suc m) = n

visible-test : visible 2 3 ≡ 2
visible-test = refl

hidden-test : hidden {2} 3 ≡ 2
hidden-test = refl

with-test : withParam 2 0 3 ≡ 2
with-test = refl

module-test : M.local 1 2 3 ≡ 2
module-test = refl
