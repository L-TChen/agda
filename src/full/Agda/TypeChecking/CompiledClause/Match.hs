{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.CompiledClause.Match where

import qualified Data.Map as Map

import Agda.Interaction.Options (optRewriting)

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad hiding (constructorForm)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute

import Agda.Utils.Maybe
import Agda.Utils.Monad
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

matchCompiled :: CompiledClauses -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Args) Term)
matchCompiled c args = do
  r <- matchCompiledE c $ map (fmap Apply) args
  case r of
    YesReduction simpl v -> return $ YesReduction simpl v
    NoReduction bes      -> return $ NoReduction $ fmap (map (fromMaybe __IMPOSSIBLE__ . isApplyElim)) bes

-- | @matchCompiledE c es@ takes a function given by case tree @c@ and
--   and a spine @es@ and tries to apply the function to @es@.
matchCompiledE :: CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Elims) Term)
matchCompiledE c args = match' [(c, args, id)]

-- | A stack entry is a triple consisting of
--   1. the part of the case tree to continue matching,
--   2. the current argument vector, and
--   3. a patch function taking the current argument vector back
--      to the original argument vector.
type Frame = (CompiledClauses, MaybeReducedElims, Elims -> Elims)
type Stack = [Frame]


-- | @match'@ tries to solve the matching problems on the @Stack@.
--   In each iteration, the top problem is removed and handled.
--
--   If the top problem was a @Done@, we succeed.
--
--   If the top problem was a @Case n@ and the @n@th argument of the problem
--   is not a constructor or literal, we are stuck, thus, fail.
--
--   If we have a branch for the constructor/literal, we put it on the stack
--   to continue.
--   If we do not have a branch, we fall through to the next problem, which
--   should be the corresponding catch-all branch.
--
--   An empty stack is an exception that can come only from an incomplete
--   function definition.

-- TODO: literal/constructor pattern conflict (for Nat)

match' :: Stack -> ReduceM (Reduced (Blocked Elims) Term)
match' ((c, es, patch) : stack) = do
  let no blocking es = return $ NoReduction $ blocking $ patch $ map ignoreReduced es
      yes t          = flip YesReduction t <$> asksTC envSimplification

  -- TODO: make this local to Done
  allowedReductions <- asksTC envAllowedReductions
  fun <- fromMaybe __IMPOSSIBLE__ <$> asksTC envAppDef
  def <- getConstInfo fun

  do

    case c of

      -- impossible case
      Fail{} -> no (NotBlocked AbsurdMatch) es

      -- done matching
      Done _no mr xs t
        | couldBeRecursive mr
        , defTerminationUnconfirmed def
        , UnconfirmedReductions `SmallSet.notMember` allowedReductions -> do
            reportSLn "tc.reduce.recursive" 80 $ "Aborting reduction of " <> prettyShow fun
            no (NotBlocked ReallyNotBlocked) es
        -- if the function was partially applied, return a lambda
        | m < n     -> yes $ applySubst (toSubst es) $ foldr lam t (drop m xs)
        -- otherwise, just apply instantiation to body
        -- apply the result to any extra arguments
        | otherwise -> yes $ applySubst (toSubst es0) t `applyE` map ignoreReduced es1
        where
          n              = length xs
          m              = length es
          -- at least the first @n@ elims must be @Apply@s, so we can
          -- turn them into a subsitution
          toSubst        = parallelS . reverse . map (unArg . fromMaybe __IMPOSSIBLE__ . isApplyElim . ignoreReduced)
          (es0, es1)     = splitAt n es
          lam x t        = Lam (argInfo x) (Abs (unArg x) t)

      -- splitting on an eta-record constructor
      Case (Arg _ n) Branches{etaBranch = Just (c, cc), catchallBranch = ca} ->
        case splitAt n es of
          (_, []) -> no (NotBlocked Underapplied) es
          (es0, MaybeRed _ e@(Apply (Arg _ v0)) : es1) ->
              let projs = [ MaybeRed NotReduced $ Apply $ Arg ai $ relToDontCare ai $ v0 `applyE` [Proj ProjSystem f] | Arg ai f <- fs ]
                  catchallFrame stack = maybe stack (\c -> (c, es, patch) : stack) ca in
              match' $ (content cc, es0 ++ projs ++ es1, patchEta) : catchallFrame stack
            where
              fs = conFields c
              patchEta es = patch (es0 ++ [e] ++ es1)
                where (es0, es') = splitAt n es
                      (_, es1)   = splitAt (length fs) es'
          _ -> __IMPOSSIBLE__

      -- splitting on the @n@th elimination
      Case (Arg _ n) bs -> do
        case splitAt n es of
          -- if the @n@th elimination is not supplied, no match
          (_, []) -> no (NotBlocked Underapplied) es
          -- if the @n@th elimination is @e0@
          (es0, MaybeRed red e0 : es1) -> do
            -- get the reduced form of @e0@
            eb :: Blocked Elim <- do
                  case red of
                    Reduced b  -> return $ e0 <$ b
                    NotReduced -> unfoldCorecursionE e0
            let e = ignoreBlocking eb
                -- replace the @n@th argument by its reduced form
                es' = es0 ++ [MaybeRed (Reduced $ () <$ eb) e] ++ es1
                -- if a catch-all clause exists, put it on the stack
                catchallFrame stack = maybe stack (\c -> (c, es', patch) : stack) (catchallBranch bs)
                -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
                litFrame l stack =
                  case Map.lookup l (litBranches bs) of
                    Nothing -> stack
                    Just cc -> (cc, es0 ++ es1, patchLit) : stack
                -- If our argument (or its constructor form) is @Con c ci vs@
                -- we push @conFrame c vs@ onto the stack.
                conFrame c ci vs stack = conFrame' (conName c) (Con c ci) vs stack
                conFrame' q f vs stack =
                  case Map.lookup q (conBranches bs) of
                    Nothing -> stack
                    Just cc -> ( content cc
                               , es0 ++ map (MaybeRed NotReduced) vs ++ es1
                               , patchCon f (length vs)
                               ) : stack
                -- If our argument is @Proj p@, we push @projFrame p@ onto the stack.
                projFrame p stack =
                  case Map.lookup p (conBranches bs) of
                    Nothing -> stack
                    Just cc -> (content cc, es0 ++ es1, patchLit) : stack
                -- The new patch function restores the @n@th argument to @v@:
                -- In case we matched a literal, just put @v@ back.
                patchLit es = patch (es0 ++ [e] ++ es1)
                  where (es0, es1) = splitAt n es
                -- In case we matched constructor @c@ with @m@ arguments,
                -- contract these @m@ arguments @vs@ to @Con c ci vs@.
--                patchCon c ci m es = patch (es0 ++ [Con c ci vs <$ e] ++ es2)
                patchCon f m es = patch (es0 ++ [f vs <$ e] ++ es2)
                  where (es0, rest) = splitAt n es
                        (es1, es2)  = splitAt m rest
                        vs          = es1
            -- zo <- do
            --    mi <- getBuiltinName' builtinIZero
            --    mo <- getBuiltinName' builtinIOne
            --    return $ Set.fromList $ catMaybes [mi,mo]

            fallThrough <- return $ Just True == fallThrough bs && isJust (catchallBranch bs)

            let
              isCon b =
                case ignoreBlocking b of
                 Apply a | c@Con{} <- unArg a -> Just c
                 _                            -> Nothing
            -- Now do the matching on the @n@ths argument:
            case eb of
              -- In case of a literal, try also its constructor form
              NotBlocked _ (Apply (Arg info v@(Lit l))) -> performedSimplification $ do
                cv <- constructorForm v
                let cFrame stack = case cv of
                      Con c ci vs -> conFrame c ci vs stack
                      _        -> stack
                match' $ litFrame l $ cFrame $ catchallFrame stack

              NotBlocked _ (Apply (Arg info v@(Def q vs))) | Just{} <- Map.lookup q (conBranches bs) -> performedSimplification $ do
                match' $ conFrame' q (Def q) vs $ catchallFrame $ stack

              -- In case of a constructor, push the conFrame
              b | Just (Con c ci vs) <- isCon b -> performedSimplification $
                match' $ conFrame c ci vs $ catchallFrame $ stack

              -- In case of a projection, push the projFrame
              NotBlocked _ (Proj _ p) -> performedSimplification $
                match' $ projFrame p $ stack -- catchallFrame $ stack
                -- Issue #1986: no catch-all for copattern matching!

              _ | fallThrough -> match' $ catchallFrame $ stack

              Blocked x _            -> no (Blocked x) es'

              -- Otherwise, we are stuck.  If we were stuck before,
              -- we keep the old reason, otherwise we give reason StuckOn here.
              NotBlocked blocked e -> no (NotBlocked $ stuckOn e blocked) es'


-- If we reach the empty stack, then pattern matching was incomplete
match' [] = {- new line here since __IMPOSSIBLE__ does not like the ' in match' -}
  caseMaybeM (asksTC envAppDef) __IMPOSSIBLE__ $ \ f -> do
    pds <- getPartialDefs
    if f `elem` pds
    then return (NoReduction $ NotBlocked (MissingClauses f) [])
    else do
      ifM (optRewriting <$> pragmaOptions)
      {-then-} (return (NoReduction $ NotBlocked ReallyNotBlocked [])) -- See #5396
      {-else-} $ traceSLn "impossible" 10
        ("Incomplete pattern matching when applying " ++ prettyShow f)
        __IMPOSSIBLE__
