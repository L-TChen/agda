module Issue6962Missing where

-- Preserve the parameter prefix when a missing definition becomes an axiom.
f (A : Set) : A -> A
