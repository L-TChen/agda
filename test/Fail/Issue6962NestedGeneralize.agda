module Issue6962NestedGeneralize where

variable A : Set

-- The outer signature has already enabled generalisation while its local
-- signature is checked. Parameter types must still reject generalisables.
f : let local (x : A) : A
        local = x
    in Set
f = Set
