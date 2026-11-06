module Issue6962Match where

open import Agda.Builtin.Nat
f {n : Nat} : Nat
f {n = zero} = zero
