module Issue6962Expression where

-- Typed binders belong to declaration heads, not ordinary applications.
bad = f (A : Set)
