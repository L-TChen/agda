module Issue6962ResultScope where

variable B : Set
f (A : Set) : B -> B
f x = helper
  where
    helper : B
    helper = x
