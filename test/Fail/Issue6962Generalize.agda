module Issue6962Generalize where

open import Agda.Primitive
variable a : Level
f (A : Set a) : A -> A
f x = x
