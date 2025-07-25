
module Agda.TypeChecking.Monad.Builtin
  ( module Agda.TypeChecking.Monad.Builtin
  , module Agda.Syntax.Builtin  -- The names are defined here.
  ) where

import Control.Monad.Except         ( MonadError(..), ExceptT )
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.Reader         ( ReaderT )
import Control.Monad.State          ( StateT )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer         ( WriterT )

import Data.Function ( on )
import qualified Data.Map as Map
import Data.Set (Set)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Builtin
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Functions  -- LEADS TO IMPORT CYCLE
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.ListT
import Agda.Utils.Monad
import Agda.Utils.Maybe
import Agda.Utils.Singleton
import Agda.Utils.Tuple
import Agda.Utils.Update

import Agda.Utils.Impossible

class ( Functor m
      , Applicative m
      , Monad m
      ) => HasBuiltins m where
  getBuiltinThing :: SomeBuiltin -> m (Maybe (Builtin PrimFun))

  default getBuiltinThing :: (MonadTrans t, HasBuiltins n, t n ~ m) => SomeBuiltin -> m (Maybe (Builtin PrimFun))
  getBuiltinThing = lift . getBuiltinThing

instance HasBuiltins m => HasBuiltins (ChangeT m)
instance HasBuiltins m => HasBuiltins (ExceptT e m)
instance HasBuiltins m => HasBuiltins (IdentityT m)
instance HasBuiltins m => HasBuiltins (ListT m)
instance HasBuiltins m => HasBuiltins (MaybeT m)
instance HasBuiltins m => HasBuiltins (ReaderT e m)
instance HasBuiltins m => HasBuiltins (StateT s m)
instance (HasBuiltins m, Monoid w) => HasBuiltins (WriterT w m)

deriving instance HasBuiltins m => HasBuiltins (BlockT m)

instance MonadIO m => HasBuiltins (TCMT m) where
  getBuiltinThing b =
    liftM2 (unionMaybeWith unionBuiltin)
      (Map.lookup b <$> useTC stLocalBuiltins)
      (Map.lookup b <$> useTC stImportedBuiltins)
{-# SPECIALIZE getBuiltinThing :: SomeBuiltin -> TCM (Maybe (Builtin PrimFun)) #-}


-- | The trivial implementation of 'HasBuiltins', using a constant 'TCState'.
--
-- This may be used instead of 'TCMT'/'ReduceM' where builtins must be accessed
-- in a pure context.
newtype BuiltinAccess a = BuiltinAccess { unBuiltinAccess :: TCState -> a }
  deriving (Functor, Applicative, Monad)

instance MonadFail BuiltinAccess where
  fail msg = BuiltinAccess $ \_ -> error msg

instance HasBuiltins BuiltinAccess where
  getBuiltinThing b = BuiltinAccess $ \state ->
    unionMaybeWith unionBuiltin
      (Map.lookup b $ state ^. stLocalBuiltins)
      (Map.lookup b $ state ^. stImportedBuiltins)

-- | Run a 'BuiltinAccess' monad.
runBuiltinAccess :: TCState -> BuiltinAccess a -> a
runBuiltinAccess s m = unBuiltinAccess m s


-- If Agda is changed so that the type of a literal can belong to an
-- inductive family (with at least one index), then the implementation
-- of split' in Agda.TypeChecking.Coverage should be changed.

litType
  :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
  => Literal -> m Type
litType = \case
  LitNat n    -> do
    _ <- primZero
    when (n > 0) $ void $ primSuc
    el <$> primNat
  LitWord64 _ -> el <$> primWord64
  LitFloat _  -> el <$> primFloat
  LitChar _   -> el <$> primChar
  LitString _ -> el <$> primString
  LitQName _  -> el <$> primQName
  LitMeta _ _ -> el <$> primAgdaMeta
  where
    el t = El (mkType 0) t

setBuiltinThings :: BuiltinThings -> TCM ()
setBuiltinThings b = stLocalBuiltins `setTCLens` b

bindBuiltinName :: BuiltinId -> Term -> TCM ()
bindBuiltinName b x = do
  builtin <- getBuiltinThing b'
  case builtin of
    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
    Just Prim{}      -> typeError $ __IMPOSSIBLE__
    Just BuiltinRewriteRelations{} -> __IMPOSSIBLE__
    Nothing          -> stLocalBuiltins `modifyTCLens` Map.insert b' (Builtin x)
  where b' = BuiltinName b

bindPrimitive :: PrimitiveId -> PrimFun -> TCM ()
bindPrimitive b pf = do
  builtin <- getBuiltinThing b'
  case builtin of
    Just (Builtin _) -> typeError $ NoSuchPrimitiveFunction (getBuiltinId b)
    Just (Prim x)    -> typeError $ (DuplicatePrimitiveBinding b `on` primFunName) x pf
    Just BuiltinRewriteRelations{} -> __IMPOSSIBLE__
    Nothing          -> stLocalBuiltins `modifyTCLens` Map.insert b' (Prim pf)
  where b' = PrimitiveName b

-- | Add one (more) relation symbol to the rewrite relations.
bindBuiltinRewriteRelation :: QName -> TCM ()
bindBuiltinRewriteRelation x =
  stLocalBuiltins `modifyTCLens`
    Map.insertWith unionBuiltin (BuiltinName builtinRewrite) (BuiltinRewriteRelations $ singleton x)

-- | Get the currently registered rewrite relation symbols.
getBuiltinRewriteRelations :: (HasBuiltins m, MonadTCError m) => m (Set QName)
getBuiltinRewriteRelations =
  fromMaybeM (typeError $ NoBindingForBuiltin builtinRewrite) getBuiltinRewriteRelations'

-- | Get the currently registered rewrite relation symbols, if any.
getBuiltinRewriteRelations' :: HasBuiltins m => m (Maybe (Set QName))
getBuiltinRewriteRelations' = fmap rels <$> getBuiltinThing (BuiltinName builtinRewrite)
  where
  rels = \case
    BuiltinRewriteRelations xs -> xs
    Prim{}    -> __IMPOSSIBLE__
    Builtin{} -> __IMPOSSIBLE__

{-# INLINABLE getBuiltinName_ #-}
getBuiltinName_ :: (HasBuiltins m, MonadTCError m)
  => BuiltinId -> m QName
getBuiltinName_ x =
  fromMaybeM (typeError $ NoBindingForBuiltin x) $ getBuiltinName' x

-- {-# INLINABLE getBuiltinName' #-}
-- -- | Returns 'Nothing' if built-in is not bound or bound to a 'Prim' or anything other than a 'Def'.
-- getBuiltinName' :: HasBuiltins m => BuiltinId -> m (Maybe Term)
-- getBuiltinName' x = (getBuiltinName =<<) <$> getBuiltin' x
--   where
--     getBuiltinName = \case
--       Def f [] -> Just f
--       _        -> Nothing

{-# INLINABLE getBuiltin #-}
getBuiltin :: (HasBuiltins m, MonadTCError m)
           => BuiltinId -> m Term
getBuiltin x =
  fromMaybeM (typeError $ NoBindingForBuiltin x) $ getBuiltin' x

{-# INLINABLE getBuiltin' #-}
-- | Returns 'Nothing' if built-in is not bound or bound to a 'Prim'.
getBuiltin' :: HasBuiltins m => BuiltinId -> m (Maybe Term)
getBuiltin' x = (getBuiltin =<<) <$> getBuiltinThing (BuiltinName x)
  where
    getBuiltin = \case
      Builtin t                 -> Just $ killRange t
      Prim{}                    -> Nothing
      BuiltinRewriteRelations{} -> __IMPOSSIBLE__

{-# INLINABLE getPrimitive' #-}
-- | Returns 'Nothing' if primitive is not bound or bound to a 'Builtin'.
getPrimitive' :: HasBuiltins m => PrimitiveId -> m (Maybe PrimFun)
getPrimitive' x = (getPrim =<<) <$> getBuiltinThing (PrimitiveName x)
  where
    getPrim = \case
      Prim pf                   -> return pf
      Builtin{}                 -> Nothing
      BuiltinRewriteRelations{} -> __IMPOSSIBLE__

{-# INLINABLE getPrimitive #-}
getPrimitive :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
             => PrimitiveId -> m PrimFun
getPrimitive x =
  fromMaybeM (typeError . NoSuchPrimitiveFunction $ getBuiltinId x) $ getPrimitive' x

getPrimitiveTerm :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
                 => PrimitiveId -> m Term
getPrimitiveTerm x = (`Def` []) . primFunName <$> getPrimitive x


getPrimitiveTerm' :: HasBuiltins m => PrimitiveId -> m (Maybe Term)
getPrimitiveTerm' x = fmap (`Def` []) <$> getPrimitiveName' x

getTerm' :: (HasBuiltins m, IsBuiltin a) => a -> m (Maybe Term)
getTerm' = go . someBuiltin where
  go (BuiltinName x)   = getBuiltin' x
  go (PrimitiveName x) = getPrimitiveTerm' x

getName' :: (HasBuiltins m, IsBuiltin a) => a -> m (Maybe QName)
getName' = go . someBuiltin where
  go (BuiltinName x)   = getBuiltinName' x
  go (PrimitiveName x) = getPrimitiveName' x

-- | @getTerm use name@ looks up @name@ as a primitive or builtin, and
-- throws an error otherwise.
-- The @use@ argument describes how the name is used for the sake of
-- the error message.
getTerm :: (HasBuiltins m, IsBuiltin a) => String -> a -> m Term
getTerm use name = flip fromMaybeM (getTerm' name) $
  return $! throwImpossible (ImpMissingDefinitions [getBuiltinId name] use)


-- | Rewrite a literal to constructor form if possible.
constructorForm :: HasBuiltins m => Term -> m Term
constructorForm v = do
  let pZero = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinZero
      pSuc  = fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSuc
  constructorForm' pZero pSuc v

{-# INLINABLE constructorForm' #-}
{-# SPECIALIZE constructorForm' :: TCM Term -> TCM Term -> Term -> TCM Term #-}
constructorForm' :: Applicative m => m Term -> m Term -> Term -> m Term
constructorForm' pZero pSuc v =
  case v of
    Lit (LitNat n)
      | n == 0    -> pZero
      | n > 0     -> (`apply1` Lit (LitNat $ n - 1)) <$> pSuc
      | otherwise -> pure v
    _ -> pure v

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger, primIntegerPos, primIntegerNegSuc,
    primFloat, primChar, primString, primUnit, primUnitUnit, primBool, primTrue, primFalse,
    primSigma,
    primList, primNil, primCons, primIO, primNat, primSuc, primZero, primMaybe, primNothing, primJust,
    primPath, primPathP, primIntervalUniv, primInterval, primIZero, primIOne, primPartial, primPartialP,
    primIMin, primIMax, primINeg,
    primIsOne, primItIsOne, primIsOne1, primIsOne2, primIsOneEmpty,
    primSub, primSubIn, primSubOut,
    primTrans, primHComp,
    primEquiv, primEquivFun, primEquivProof,
    primTranspProof,
    primGlue, prim_glue, prim_unglue,
    prim_glueU, prim_unglueU,
    primFaceForall,
    primNatPlus, primNatMinus, primNatTimes, primNatDivSucAux, primNatModSucAux,
    primNatEquality, primNatLess,
    -- Machine words
    primWord64,
    primSizeUniv, primSize, primSizeLt, primSizeSuc, primSizeInf, primSizeMax,
    primInf, primSharp, primFlat,
    primEquality, primRefl,
    primLevel, primLevelZero, primLevelSuc, primLevelMax,
    primLockUniv,
    primLevelUniv,
    primProp, primSet, primStrictSet, primPropOmega, primSetOmega, primSSetOmega,
    primFromNat, primFromNeg, primFromString,
    -- builtins for reflection:
    primQName, primArgInfo, primArgArgInfo, primArg, primArgArg, primAbs, primAbsAbs, primAgdaTerm, primAgdaTermVar,
    primAgdaTermLam, primAgdaTermExtLam, primAgdaTermDef, primAgdaTermCon, primAgdaTermPi,
    primAgdaTermSort, primAgdaTermLit, primAgdaTermUnsupported, primAgdaTermMeta,
    primAgdaErrorPart, primAgdaErrorPartString, primAgdaErrorPartTerm, primAgdaErrorPartPatt, primAgdaErrorPartName,
    primHiding, primHidden, primInstance, primVisible,
    primRelevance, primRelevant, primIrrelevant,
    primQuantity, primQuantity0, primQuantityω,
    primModality, primModalityConstructor,
    primAssoc, primAssocLeft, primAssocRight, primAssocNon,
    primPrecedence, primPrecRelated, primPrecUnrelated,
    primFixity, primFixityFixity,
    primAgdaLiteral, primAgdaLitNat, primAgdaLitWord64, primAgdaLitFloat, primAgdaLitString, primAgdaLitChar, primAgdaLitQName, primAgdaLitMeta,
    primAgdaSort, primAgdaSortSet, primAgdaSortLit, primAgdaSortProp, primAgdaSortPropLit, primAgdaSortInf, primAgdaSortUnsupported,
    primAgdaDefinition, primAgdaDefinitionFunDef, primAgdaDefinitionDataDef, primAgdaDefinitionRecordDef,
    primAgdaDefinitionPostulate, primAgdaDefinitionPrimitive, primAgdaDefinitionDataConstructor,
    primAgdaClause, primAgdaClauseClause, primAgdaClauseAbsurd,
    primAgdaPattern, primAgdaPatCon, primAgdaPatVar, primAgdaPatDot,
    primAgdaPatLit, primAgdaPatProj,
    primAgdaPatAbsurd,
    primAgdaMeta,
    primAgdaBlocker, primAgdaBlockerAny, primAgdaBlockerAll, primAgdaBlockerMeta,
    primAgdaTCM, primAgdaTCMReturn, primAgdaTCMBind, primAgdaTCMUnify,
    primAgdaTCMTypeError, primAgdaTCMInferType, primAgdaTCMCheckType,
    primAgdaTCMNormalise, primAgdaTCMReduce,
    primAgdaTCMCatchError, primAgdaTCMGetContext, primAgdaTCMExtendContext, primAgdaTCMInContext,
    primAgdaTCMFreshName, primAgdaTCMDeclareDef, primAgdaTCMDeclarePostulate, primAgdaTCMDeclareData, primAgdaTCMDefineData, primAgdaTCMDefineFun,
    primAgdaTCMGetType, primAgdaTCMGetDefinition,
    primAgdaTCMQuoteTerm, primAgdaTCMUnquoteTerm, primAgdaTCMQuoteOmegaTerm,
    primAgdaTCMCommit, primAgdaTCMIsMacro, primAgdaTCMBlock,
    primAgdaTCMFormatErrorParts, primAgdaTCMDebugPrint,
    primAgdaTCMWithNormalisation, primAgdaTCMWithReconstructed,
    primAgdaTCMWithExpandLast, primAgdaTCMWithReduceDefs,
    primAgdaTCMAskNormalisation, primAgdaTCMAskReconstructed,
    primAgdaTCMAskExpandLast, primAgdaTCMAskReduceDefs,
    primAgdaTCMNoConstraints,
    primAgdaTCMWorkOnTypes,
    primAgdaTCMRunSpeculative,
    primAgdaTCMExec,
    primAgdaTCMCheckFromString,
    primAgdaTCMGetInstances,
    primAgdaTCMSolveInstances,
    primAgdaTCMPragmaForeign,
    primAgdaTCMPragmaCompile
    :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Term

primInteger                           = getBuiltin builtinInteger
primIntegerPos                        = getBuiltin builtinIntegerPos
primIntegerNegSuc                     = getBuiltin builtinIntegerNegSuc
primFloat                             = getBuiltin builtinFloat
primChar                              = getBuiltin builtinChar
primString                            = getBuiltin builtinString
primBool                              = getBuiltin builtinBool
primSigma                             = getBuiltin builtinSigma
primUnit                              = getBuiltin builtinUnit
primUnitUnit                          = getBuiltin builtinUnitUnit
primTrue                              = getBuiltin builtinTrue
primFalse                             = getBuiltin builtinFalse
primList                              = getBuiltin builtinList
primNil                               = getBuiltin builtinNil
primCons                              = getBuiltin builtinCons
primMaybe                             = getBuiltin builtinMaybe
primNothing                           = getBuiltin builtinNothing
primJust                              = getBuiltin builtinJust
primIO                                = getBuiltin builtinIO
primPath                              = getBuiltin builtinPath
primPathP                             = getBuiltin builtinPathP
primIntervalUniv                      = getBuiltin builtinIntervalUniv
primInterval                          = getBuiltin builtinInterval
primIZero                             = getBuiltin builtinIZero
primIOne                              = getBuiltin builtinIOne
primIMin                              = getPrimitiveTerm builtinIMin
primIMax                              = getPrimitiveTerm builtinIMax
primINeg                              = getPrimitiveTerm builtinINeg
primPartial                           = getPrimitiveTerm PrimPartial
primPartialP                          = getPrimitiveTerm PrimPartialP
primIsOne                             = getBuiltin builtinIsOne
primItIsOne                           = getBuiltin builtinItIsOne
primTrans                             = getPrimitiveTerm builtinTrans
primHComp                             = getPrimitiveTerm builtinHComp
primEquiv                             = getBuiltin builtinEquiv
primEquivFun                          = getBuiltin builtinEquivFun
primEquivProof                        = getBuiltin builtinEquivProof
primTranspProof                       = getBuiltin builtinTranspProof
prim_glueU                            = getPrimitiveTerm builtin_glueU
prim_unglueU                          = getPrimitiveTerm builtin_unglueU
primGlue                              = getPrimitiveTerm builtinGlue
prim_glue                             = getPrimitiveTerm builtin_glue
prim_unglue                           = getPrimitiveTerm builtin_unglue
primFaceForall                        = getPrimitiveTerm builtinFaceForall
primIsOne1                            = getBuiltin builtinIsOne1
primIsOne2                            = getBuiltin builtinIsOne2
primIsOneEmpty                        = getBuiltin builtinIsOneEmpty
primSub                               = getBuiltin builtinSub
primSubIn                             = getBuiltin builtinSubIn
primSubOut                            = getPrimitiveTerm builtinSubOut
primNat                               = getBuiltin builtinNat
primSuc                               = getBuiltin builtinSuc
primZero                              = getBuiltin builtinZero
primNatPlus                           = getBuiltin builtinNatPlus
primNatMinus                          = getBuiltin builtinNatMinus
primNatTimes                          = getBuiltin builtinNatTimes
primNatDivSucAux                      = getBuiltin builtinNatDivSucAux
primNatModSucAux                      = getBuiltin builtinNatModSucAux
primNatEquality                       = getBuiltin builtinNatEquals
primNatLess                           = getBuiltin builtinNatLess
primWord64                            = getBuiltin builtinWord64
primSizeUniv                          = getBuiltin builtinSizeUniv
primSize                              = getBuiltin builtinSize
primSizeLt                            = getBuiltin builtinSizeLt
primSizeSuc                           = getBuiltin builtinSizeSuc
primSizeInf                           = getBuiltin builtinSizeInf
primSizeMax                           = getBuiltin builtinSizeMax
primInf                               = getBuiltin builtinInf
primSharp                             = getBuiltin builtinSharp
primFlat                              = getBuiltin builtinFlat
primEquality                          = getBuiltin builtinEquality
primRefl                              = getBuiltin builtinRefl
primLevel                             = getBuiltin builtinLevel
primLevelZero                         = getBuiltin builtinLevelZero
primLevelSuc                          = getBuiltin builtinLevelSuc
primLevelMax                          = getBuiltin builtinLevelMax
primProp                              = getBuiltin builtinProp
primSet                               = getBuiltin builtinSet
primStrictSet                         = getBuiltin builtinStrictSet
primPropOmega                         = getBuiltin builtinPropOmega
primSetOmega                          = getBuiltin builtinSetOmega
primSSetOmega                         = getBuiltin builtinSSetOmega
primLockUniv                          = getPrimitiveTerm builtinLockUniv
primLevelUniv                         = getBuiltin builtinLevelUniv
primFromNat                           = getBuiltin builtinFromNat
primFromNeg                           = getBuiltin builtinFromNeg
primFromString                        = getBuiltin builtinFromString
primQName                             = getBuiltin builtinQName
primArg                               = getBuiltin builtinArg
primArgArg                            = getBuiltin builtinArgArg
primAbs                               = getBuiltin builtinAbs
primAbsAbs                            = getBuiltin builtinAbsAbs
primAgdaSort                          = getBuiltin builtinAgdaSort
primHiding                            = getBuiltin builtinHiding
primHidden                            = getBuiltin builtinHidden
primInstance                          = getBuiltin builtinInstance
primVisible                           = getBuiltin builtinVisible
primRelevance                         = getBuiltin builtinRelevance
primRelevant                          = getBuiltin builtinRelevant
primIrrelevant                        = getBuiltin builtinIrrelevant
primQuantity                          = getBuiltin builtinQuantity
primQuantity0                         = getBuiltin builtinQuantity0
primQuantityω                         = getBuiltin builtinQuantityω
primModality                          = getBuiltin builtinModality
primModalityConstructor               = getBuiltin builtinModalityConstructor
primAssoc                             = getBuiltin builtinAssoc
primAssocLeft                         = getBuiltin builtinAssocLeft
primAssocRight                        = getBuiltin builtinAssocRight
primAssocNon                          = getBuiltin builtinAssocNon
primPrecedence                        = getBuiltin builtinPrecedence
primPrecRelated                       = getBuiltin builtinPrecRelated
primPrecUnrelated                     = getBuiltin builtinPrecUnrelated
primFixity                            = getBuiltin builtinFixity
primFixityFixity                      = getBuiltin builtinFixityFixity
primAgdaBlocker                       = getBuiltin builtinAgdaBlocker
primAgdaBlockerAny                    = getBuiltin builtinAgdaBlockerAny
primAgdaBlockerAll                    = getBuiltin builtinAgdaBlockerAll
primAgdaBlockerMeta                   = getBuiltin builtinAgdaBlockerMeta
primArgInfo                           = getBuiltin builtinArgInfo
primArgArgInfo                        = getBuiltin builtinArgArgInfo
primAgdaSortSet                       = getBuiltin builtinAgdaSortSet
primAgdaSortLit                       = getBuiltin builtinAgdaSortLit
primAgdaSortProp                      = getBuiltin builtinAgdaSortProp
primAgdaSortPropLit                   = getBuiltin builtinAgdaSortPropLit
primAgdaSortInf                       = getBuiltin builtinAgdaSortInf
primAgdaSortUnsupported               = getBuiltin builtinAgdaSortUnsupported
primAgdaTerm                          = getBuiltin builtinAgdaTerm
primAgdaTermVar                       = getBuiltin builtinAgdaTermVar
primAgdaTermLam                       = getBuiltin builtinAgdaTermLam
primAgdaTermExtLam                    = getBuiltin builtinAgdaTermExtLam
primAgdaTermDef                       = getBuiltin builtinAgdaTermDef
primAgdaTermCon                       = getBuiltin builtinAgdaTermCon
primAgdaTermPi                        = getBuiltin builtinAgdaTermPi
primAgdaTermSort                      = getBuiltin builtinAgdaTermSort
primAgdaTermLit                       = getBuiltin builtinAgdaTermLit
primAgdaTermUnsupported               = getBuiltin builtinAgdaTermUnsupported
primAgdaTermMeta                      = getBuiltin builtinAgdaTermMeta
primAgdaErrorPart                     = getBuiltin builtinAgdaErrorPart
primAgdaErrorPartString               = getBuiltin builtinAgdaErrorPartString
primAgdaErrorPartTerm                 = getBuiltin builtinAgdaErrorPartTerm
primAgdaErrorPartPatt                 = getBuiltin builtinAgdaErrorPartPatt
primAgdaErrorPartName                 = getBuiltin builtinAgdaErrorPartName
primAgdaLiteral                       = getBuiltin builtinAgdaLiteral
primAgdaLitNat                        = getBuiltin builtinAgdaLitNat
primAgdaLitWord64                     = getBuiltin builtinAgdaLitWord64
primAgdaLitFloat                      = getBuiltin builtinAgdaLitFloat
primAgdaLitChar                       = getBuiltin builtinAgdaLitChar
primAgdaLitString                     = getBuiltin builtinAgdaLitString
primAgdaLitQName                      = getBuiltin builtinAgdaLitQName
primAgdaLitMeta                       = getBuiltin builtinAgdaLitMeta
primAgdaPattern                       = getBuiltin builtinAgdaPattern
primAgdaPatCon                        = getBuiltin builtinAgdaPatCon
primAgdaPatVar                        = getBuiltin builtinAgdaPatVar
primAgdaPatDot                        = getBuiltin builtinAgdaPatDot
primAgdaPatLit                        = getBuiltin builtinAgdaPatLit
primAgdaPatProj                       = getBuiltin builtinAgdaPatProj
primAgdaPatAbsurd                     = getBuiltin builtinAgdaPatAbsurd
primAgdaClause                        = getBuiltin builtinAgdaClause
primAgdaClauseClause                  = getBuiltin builtinAgdaClauseClause
primAgdaClauseAbsurd                  = getBuiltin builtinAgdaClauseAbsurd
primAgdaDefinitionFunDef              = getBuiltin builtinAgdaDefinitionFunDef
primAgdaDefinitionDataDef             = getBuiltin builtinAgdaDefinitionDataDef
primAgdaDefinitionRecordDef           = getBuiltin builtinAgdaDefinitionRecordDef
primAgdaDefinitionDataConstructor     = getBuiltin builtinAgdaDefinitionDataConstructor
primAgdaDefinitionPostulate           = getBuiltin builtinAgdaDefinitionPostulate
primAgdaDefinitionPrimitive           = getBuiltin builtinAgdaDefinitionPrimitive
primAgdaDefinition                    = getBuiltin builtinAgdaDefinition
primAgdaMeta                          = getBuiltin builtinAgdaMeta
primAgdaTCM                           = getBuiltin builtinAgdaTCM
primAgdaTCMReturn                     = getBuiltin builtinAgdaTCMReturn
primAgdaTCMBind                       = getBuiltin builtinAgdaTCMBind
primAgdaTCMUnify                      = getBuiltin builtinAgdaTCMUnify
primAgdaTCMTypeError                  = getBuiltin builtinAgdaTCMTypeError
primAgdaTCMInferType                  = getBuiltin builtinAgdaTCMInferType
primAgdaTCMCheckType                  = getBuiltin builtinAgdaTCMCheckType
primAgdaTCMNormalise                  = getBuiltin builtinAgdaTCMNormalise
primAgdaTCMReduce                     = getBuiltin builtinAgdaTCMReduce
primAgdaTCMCatchError                 = getBuiltin builtinAgdaTCMCatchError
primAgdaTCMGetContext                 = getBuiltin builtinAgdaTCMGetContext
primAgdaTCMExtendContext              = getBuiltin builtinAgdaTCMExtendContext
primAgdaTCMInContext                  = getBuiltin builtinAgdaTCMInContext
primAgdaTCMFreshName                  = getBuiltin builtinAgdaTCMFreshName
primAgdaTCMDeclareDef                 = getBuiltin builtinAgdaTCMDeclareDef
primAgdaTCMDeclarePostulate           = getBuiltin builtinAgdaTCMDeclarePostulate
primAgdaTCMDeclareData                = getBuiltin builtinAgdaTCMDeclareData
primAgdaTCMDefineData                 = getBuiltin builtinAgdaTCMDefineData
primAgdaTCMDefineFun                  = getBuiltin builtinAgdaTCMDefineFun
primAgdaTCMGetType                    = getBuiltin builtinAgdaTCMGetType
primAgdaTCMGetDefinition              = getBuiltin builtinAgdaTCMGetDefinition
primAgdaTCMQuoteTerm                  = getBuiltin builtinAgdaTCMQuoteTerm
primAgdaTCMQuoteOmegaTerm             = getBuiltin builtinAgdaTCMQuoteOmegaTerm
primAgdaTCMUnquoteTerm                = getBuiltin builtinAgdaTCMUnquoteTerm
primAgdaTCMBlock                      = getBuiltin builtinAgdaTCMBlock
primAgdaTCMCommit                     = getBuiltin builtinAgdaTCMCommit
primAgdaTCMIsMacro                    = getBuiltin builtinAgdaTCMIsMacro
primAgdaTCMWithNormalisation          = getBuiltin builtinAgdaTCMWithNormalisation
primAgdaTCMWithReconstructed          = getBuiltin builtinAgdaTCMWithReconstructed
primAgdaTCMWithExpandLast             = getBuiltin builtinAgdaTCMWithExpandLast
primAgdaTCMWithReduceDefs             = getBuiltin builtinAgdaTCMWithReduceDefs
primAgdaTCMAskNormalisation           = getBuiltin builtinAgdaTCMAskNormalisation
primAgdaTCMAskReconstructed           = getBuiltin builtinAgdaTCMAskReconstructed
primAgdaTCMAskExpandLast              = getBuiltin builtinAgdaTCMAskExpandLast
primAgdaTCMAskReduceDefs              = getBuiltin builtinAgdaTCMAskReduceDefs
primAgdaTCMFormatErrorParts           = getBuiltin builtinAgdaTCMFormatErrorParts
primAgdaTCMDebugPrint                 = getBuiltin builtinAgdaTCMDebugPrint
primAgdaTCMNoConstraints              = getBuiltin builtinAgdaTCMNoConstraints
primAgdaTCMWorkOnTypes                = getBuiltin builtinAgdaTCMWorkOnTypes
primAgdaTCMRunSpeculative             = getBuiltin builtinAgdaTCMRunSpeculative
primAgdaTCMExec                       = getBuiltin builtinAgdaTCMExec
primAgdaTCMCheckFromString            = getBuiltin builtinAgdaTCMCheckFromString
primAgdaTCMGetInstances               = getBuiltin builtinAgdaTCMGetInstances
primAgdaTCMSolveInstances             = getBuiltin builtinAgdaTCMSolveInstances
primAgdaTCMPragmaForeign              = getBuiltin builtinAgdaTCMPragmaForeign
primAgdaTCMPragmaCompile              = getBuiltin builtinAgdaTCMPragmaCompile

-- | The coinductive primitives.

data CoinductionKit = CoinductionKit
  { nameOfInf   :: QName
  , nameOfSharp :: QName
  , nameOfFlat  :: QName
  }

-- | Tries to build a 'CoinductionKit'.

coinductionKit' :: TCM CoinductionKit
coinductionKit' = do
  inf   <- getBuiltinName_ builtinInf
  sharp <- getBuiltinName_ builtinSharp
  flat  <- getBuiltinName_ builtinFlat
  return $ CoinductionKit
    { nameOfInf   = inf
    , nameOfSharp = sharp
    , nameOfFlat  = flat
    }

coinductionKit :: TCM (Maybe CoinductionKit)
coinductionKit = tryMaybe coinductionKit'

-- | Sort primitives.

data SortKit = SortKit
  { nameOfUniv   :: UnivSize -> Univ -> QName
  , isNameOfUniv :: QName -> Maybe (UnivSize, Univ)
  }

mkSortKit :: QName -> QName -> QName -> QName -> QName -> QName -> SortKit
mkSortKit prop set sset propomega setomega ssetomega = SortKit
  { nameOfUniv = curry $ \case
      (USmall , UProp) -> prop
      (USmall , UType) -> set
      (USmall , USSet) -> sset
      (ULarge , UProp) -> propomega
      (ULarge , UType) -> setomega
      (ULarge , USSet) -> ssetomega
  , isNameOfUniv = \ x -> if
      | x == prop      -> Just (USmall , UProp)
      | x == set       -> Just (USmall , UType)
      | x == sset      -> Just (USmall , USSet)
      | x == propomega -> Just (ULarge , UProp)
      | x == setomega  -> Just (ULarge , UType)
      | x == ssetomega -> Just (ULarge , USSet)
      | otherwise -> Nothing
  }

-- | Compute a 'SortKit' in an environment that supports failures.
--
-- When 'optLoadPrimitives' is set to 'False', 'sortKit' is a fallible operation,
-- so for the uses of 'sortKit' in fallible contexts (e.g. 'TCM'),
-- we report a type error rather than exploding.
sortKit :: (HasBuiltins m, MonadTCError m, HasOptions m) => m SortKit
sortKit = do
  prop      <- getBuiltinName_ builtinProp
  set       <- getBuiltinName_ builtinSet
  sset      <- getBuiltinName_ builtinStrictSet
  propomega <- getBuiltinName_ builtinPropOmega
  setomega  <- getBuiltinName_ builtinSetOmega
  ssetomega <- getBuiltinName_ builtinSSetOmega
  return $ mkSortKit prop set sset propomega setomega ssetomega

-- | Compute a 'SortKit' in contexts that do not support failure (e.g.
-- 'Reify'). This should only be used when we are sure that the
-- primitive sorts have been bound, i.e. because it is "after" type
-- checking.
infallibleSortKit :: HasBuiltins m => m SortKit
infallibleSortKit = do
  prop      <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinProp
  set       <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
  sset      <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinStrictSet
  propomega <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinPropOmega
  setomega  <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSetOmega
  ssetomega <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSSetOmega
  return $ mkSortKit prop set sset propomega setomega ssetomega

------------------------------------------------------------------------
-- * Path equality
------------------------------------------------------------------------

getPrimName :: Term -> QName
getPrimName ty = do
  let lamV (Lam i b)  = mapFst (getHiding i :) $ lamV (unAbs b)
      lamV (Pi _ b)   = lamV (unEl $ unAbs b)
      lamV v          = ([], v)
  case lamV ty of
            (_, Def path _) -> path
            (_, Con nm _ _)   -> conName nm
            (_, Var 0 [Proj _ l]) -> l
            (_, t)          -> __IMPOSSIBLE__

getBuiltinName' :: HasBuiltins m => BuiltinId -> m (Maybe QName)
getBuiltinName' n = fmap getPrimName <$> getBuiltin' n

getPrimitiveName' :: HasBuiltins m => PrimitiveId -> m (Maybe QName)
getPrimitiveName' n = fmap primFunName <$> getPrimitive' n

isPrimitive :: HasBuiltins m => PrimitiveId -> QName -> m Bool
isPrimitive n q = (Just q ==) <$> getPrimitiveName' n

intervalSort :: Sort
intervalSort = IntervalUniv

{-# SPECIALIZE intervalView' :: TCM (Term -> IntervalView) #-}
{-# INLINABLE intervalView' #-}
intervalView' :: HasBuiltins m => m (Term -> IntervalView)
intervalView' = do
  iz <- getBuiltinName' builtinIZero
  io <- getBuiltinName' builtinIOne
  imax <- getPrimitiveName' builtinIMax
  imin <- getPrimitiveName' builtinIMin
  ineg <- getPrimitiveName' builtinINeg
  return $ \ t ->
    case t of
      Def q es ->
        case es of
          [Apply x,Apply y] | Just q == imin -> IMin x y
          [Apply x,Apply y] | Just q == imax -> IMax x y
          [Apply x]         | Just q == ineg -> INeg x
          _                 -> OTerm t
      Con q _ [] | Just (conName q) == iz -> IZero
                 | Just (conName q) == io -> IOne
      _ -> OTerm t

{-# INLINE intervalView #-}
intervalView :: HasBuiltins m => Term -> m IntervalView
intervalView t = do
  f <- intervalView'
  return (f t)

intervalUnview :: HasBuiltins m => IntervalView -> m Term
intervalUnview t = do
  f <- intervalUnview'
  return (f t)

{-# SPECIALIZE intervalUnview' :: TCM (IntervalView -> Term) #-}
intervalUnview' :: HasBuiltins m => m (IntervalView -> Term)
intervalUnview' = do
  iz <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIZero -- should it be a type error instead?
  io <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIOne
  imin <- (`Def` []) . fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinIMin
  imax <- (`Def` []) . fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinIMax
  ineg <- (`Def` []) . fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinINeg
  return $ \ v -> case v of
             IZero -> iz
             IOne  -> io
             IMin x y -> apply imin [x,y]
             IMax x y -> apply imax [x,y]
             INeg x   -> apply ineg [x]
             OTerm t -> t

------------------------------------------------------------------------
-- * Path equality
------------------------------------------------------------------------

-- | Check whether the type is actually an path (lhs ≡ rhs)
--   and extract lhs, rhs, and their type.
--
--   Precondition: type is reduced.

{-# INLINE pathView #-}
pathView :: HasBuiltins m => Type -> m PathView
pathView t0 = do
  view <- pathView'
  return $ view t0

{-# SPECIALIZE pathView' :: TCM (Type -> PathView)  #-}
pathView' :: HasBuiltins m => m (Type -> PathView)
pathView' = do
 mpath  <- getBuiltinName' builtinPath
 mpathp <- getBuiltinName' builtinPathP
 return $ \ t0@(El s t) ->
  case t of
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | Just path' == mpath, Just path <- mpathp -> PathType s path level (lam_i <$> typ) lhs rhs
      where lam_i = Lam defaultArgInfo . NoAbs "_"
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | Just path' == mpathp, Just path <- mpathp -> PathType s path level typ lhs rhs
    _ -> OType t0

boldPathView :: Type -> PathView
boldPathView t0@(El s t) = do
  case t of
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      -> PathType s path' level typ lhs rhs
    _ -> OType t0

-- | Revert the 'PathView'.
--
--   Postcondition: type is reduced.

pathUnview :: PathView -> Type
pathUnview (OType t) = t
pathUnview (PathType s path l t lhs rhs) =
  El s $ Def path $ map Apply [l, t, lhs, rhs]

------------------------------------------------------------------------
-- * Builtin equality
------------------------------------------------------------------------

-- | Get the name of the equality type.
primEqualityName :: TCM QName
primEqualityName = do
  eq <- primEquality
  -- Andreas, 2014-05-17 moved this here from TC.Rules.Def
  -- Don't know why up to 2 hidden lambdas need to be stripped,
  -- but I left the code in place.
  -- Maybe it was intended that equality could be declared
  -- in three different ways:
  -- 1. universe and type polymorphic
  -- 2. type polymorphic only
  -- 3. monomorphic.
  let lamV (Lam i b)  = mapFst (getHiding i :) $ lamV (unAbs b)
      lamV v          = ([], v)
  return $ case lamV eq of
    (_, Def equality _) -> equality
    _                   -> __IMPOSSIBLE__

-- | Check whether the type is actually an equality (lhs ≡ rhs)
--   and extract lhs, rhs, and their type.
--
--   Precondition: type is reduced.

equalityView ::
     Range  -- ^ Range of the @rewrite@ expression, if any.
  -> Type   -- ^ Identity type?
  -> TCM EqualityView
equalityView r t0@(El s t) = do
  equality <- primEqualityName
  case t of
    Def equality' es | equality' == equality -> do
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      let n = length vs
      unless (n >= 3) __IMPOSSIBLE__
      let (pars, [ typ , lhs, rhs ]) = splitAt (n-3) vs
      return $ EqualityType r s equality pars typ lhs rhs
    _ -> return $ OtherType t0

-- | Revert the 'EqualityView'.
--
--   Postcondition: type is reduced.

class EqualityUnview a where
  equalityUnview :: a -> Type

instance EqualityUnview EqualityView where
  equalityUnview = \case
    OtherType t -> t
    IdiomType t -> t
    EqualityViewType eqt -> equalityUnview eqt

instance EqualityUnview EqualityTypeData where
  equalityUnview (EqualityTypeData _r s equality l t lhs rhs) =
    El s $ Def equality $ map Apply (l ++ [t, lhs, rhs])

-- | Primitives with typechecking constrants.
constrainedPrims :: [PrimitiveId]
constrainedPrims =
  [ builtinPOr
  , builtinComp
  , builtinHComp
  , builtinTrans
  , builtin_glue
  , builtin_glueU
  ]

getNameOfConstrained :: HasBuiltins m => PrimitiveId -> m (Maybe QName)
getNameOfConstrained s = do
  unless (s `elem` constrainedPrims) __IMPOSSIBLE__
  getName' s
