{-# OPTIONS --erasure #-}

module Issue6962Import where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
import Issue6962 as P

-- The public type, including external binder names, survives serialization.
imported : P.renamed {B = Nat} 4 ≡ 4
imported = refl

module M = P.UnderModule Nat
instantiated : M.local 3 ≡ 3
instantiated = refl
