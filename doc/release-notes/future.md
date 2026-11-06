NOTE: Put drafts of release notes here that might be included in some
future release.

Language
--------

* Function signatures can introduce definition parameters before the colon:

  ```agda
  id {A : Set} : A → A
  id x = x
  ```

  Parameters scope over the signature and clauses, and are omitted from
  clause left-hand sides. Calls, including recursive calls, pass them as
  ordinary arguments. At least one parameter must have a type annotation;
  generalisable variables in parameter types must be bound explicitly.
  Postulate and field declarations do not support this syntax.

  See [#6962](https://github.com/agda/agda/issues/6962).

Pragmas and Options
-------------------

* The option `--termination-depth` is now obsolete.

  The default termination depth is now infinity instead of
  (previously) 1.  This means that setting `--termination-depth` might
  now make the termination checker *weaker* (instead of stronger).
  However, there is no guaranteed effect of setting
  `--termination-depth` any more.  The flag is only kept for debugging
  Agda.

  For example, the following code now passes the termination checker
  (needed higher `--termination-depth` before):

  ```agda
  f : Nat → Nat
  g : Nat → Nat

  f zero                = zero
  f (suc zero)          = zero
  f (suc (suc zero))    = zero
  f (suc (suc (suc n))) = g n     -- decrease by 3

  g n = f (suc (suc n))           -- increase by 2
  ```

  [See also Issue [#709](https://github.com/agda/agda/issues/709)]

