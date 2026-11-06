module Issue6962 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

visible (n : Nat) : Nat -> Nat
visible m = {!n!}

hidden {n : Nat} : Nat -> Nat
hidden m = {!n!}

withParam (n : Nat) : Nat -> Nat -> Nat
withParam m k with m
... | zero = {!n!}
... | suc m = n

rewriteParam (n : Nat) : n ≡ n -> Nat -> Nat
rewriteParam eq m rewrite eq = {!n!}

module M (p : Nat) where
  local (n : Nat) : Nat -> Nat
  local m = {!n!}
