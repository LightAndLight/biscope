{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
module Main where

import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad (ap, unless)
import Data.Bifunctor (Bifunctor(..))
import Data.Deriving (deriveEq1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (eq1, eq2, showsPrec1, showsPrec2)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Biscope
import Bisubst.Class

data Kind ki
  = KindVar ki
  | KindArr (Kind ki) (Kind ki)
  | KindType
  deriving (Functor, Foldable, Traversable)
makeBound ''Kind
deriveEq1 ''Kind
deriveShow1 ''Kind

instance Eq ki => Eq (Kind ki) where; (==) = eq1
instance Show ki => Show (Kind ki) where; showsPrec = showsPrec1

instance Pretty ki => Pretty (Kind ki) where
  pretty ki =
    case ki of
      KindVar a -> pretty a
      KindArr a b ->
        Pretty.hsep
        [ (case a of; KindArr{} -> Pretty.parens; _ -> id) (pretty a)
        , Pretty.text "->"
        , pretty b
        ]
      KindType -> Pretty.text "Type"

data Ty ki ty
  = TyVar ty
  | TyApp (Ty ki ty) (Ty ki ty)
  | TyForall (Kind ki) (BiscopeR () Kind Ty ki ty)
  | TyExists (Kind ki) (BiscopeR () Kind Ty ki ty)
  | TyArr
  | TyCtor String
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''Ty
deriveShow2 ''Ty
deriveEq1 ''Ty
deriveShow1 ''Ty

prettyTy ::
  Pretty ki =>
  (ty -> Doc) ->
  [Int] ->
  Ty ki ty ->
  Doc
prettyTy prettyVar supply ty =
  case ty of
    TyVar a -> prettyVar a
    TyApp (TyApp TyArr a) b ->
      Pretty.hsep
      [ (case a of
          TyApp (TyApp TyArr _) _ -> Pretty.parens
          _ -> id)
        (prettyTy prettyVar supply a)
      , Pretty.text "->"
      , prettyTy prettyVar supply b
      ]
    TyApp a b ->
      Pretty.hsep
      [ (case a of
          TyForall{} -> Pretty.parens
          TyExists{} -> Pretty.parens
          _ -> id)
        (prettyTy prettyVar supply a)
      , (case b of
          TyForall{} -> Pretty.parens
          TyExists{} -> Pretty.parens
          TyApp{} -> Pretty.parens
          _ -> id)
        (prettyTy prettyVar supply b)
      ]
    TyForall a b ->
      case supply of
        [] -> undefined
        name : supply' ->
          let
            var = Pretty.text "t" <> Pretty.int name
          in
            Pretty.char '∀' <>
            Pretty.parens
              (Pretty.hsep
              [ var
              , Pretty.char ':'
              , pretty a
              ]) <>
            Pretty.char '.' <> Pretty.space <>
            prettyTy (unvar (const var) prettyVar) supply' (fromBiscopeR b)
    TyExists a b ->
      case supply of
        [] -> undefined
        name : supply' ->
          let
            var = Pretty.text "t" <> Pretty.int name
          in
            Pretty.char '∃' <>
            Pretty.parens
              (Pretty.hsep
              [ var
              , Pretty.char ':'
              , pretty a
              ]) <>
            Pretty.char '.' <> Pretty.space <>
            prettyTy (unvar (const var) prettyVar) supply' (fromBiscopeR b)
    TyArr -> Pretty.text "(->)"
    TyCtor a -> Pretty.text a

instance (Pretty ki, Pretty ty) => Pretty (Ty ki ty) where
  pretty = prettyTy pretty [0..]

instance Applicative (Ty ki) where; pure = return; (<*>) = ap
instance Monad (Ty ki) where
  return = TyVar
  (>>=) ty f =
    case ty of
      TyVar a -> f a
      TyApp a b -> TyApp (a >>= f) (b >>= f)
      TyForall a b -> TyForall a (substBiscopeR f b)
      TyExists a b -> TyExists a (substBiscopeR f b)
      TyArr -> TyArr
      TyCtor a -> TyCtor a

instance (Eq ki, Eq ty) => Eq (Ty ki ty) where; (==) = eq2
instance (Show ki, Show ty) => Show (Ty ki ty) where; showsPrec = showsPrec2

instance Bifunctor Ty where; bimap = bisubstBimapDefault
instance Bisubst Ty Kind where
  bireturn = TyVar
  bisubst f g ty =
    case ty of
      TyVar a -> g a
      TyApp a b -> TyApp (bisubst f g a) (bisubst f g b)
      TyForall a b -> TyForall (a >>= f) (bisubstBiscopeR f g b)
      TyExists a b -> TyExists (a >>= f) (bisubstBiscopeR f g b)
      TyArr -> TyArr
      TyCtor a -> TyCtor a

data Tm ki ty tm
  = TmVar tm
  | TmAnn (Tm ki ty tm) (Ty ki ty)

  -- Value abstraction
  | TmLamTm (Ty ki ty) (BiscopeR () (Ty ki) (Tm ki) ty tm)
  -- Value application
  | TmAppTm (Tm ki ty tm) (Tm ki ty tm)

  -- Type abstraction
  | TmLamTy (Kind ki) (BiscopeL () (Ty ki) (Tm ki) ty tm)
  -- Type application
  | TmAppTy (Tm ki ty tm) (Ty ki ty)

  -- Existential introduction
  | TmPack (Ty ki ty) (Tm ki ty tm)
  -- Existential elimination
  | TmOpen (Tm ki ty tm) (Biscope2 () () (Ty ki) (Tm ki) ty tm)
  deriving (Functor, Foldable, Traversable)
deriveEq2 ''Tm
deriveShow2 ''Tm

instance (Pretty ki, Pretty ty, Pretty tm) => Pretty (Tm ki ty tm) where
  pretty = go pretty pretty [0..] [0..]
    where
      go ::
        Pretty ki =>
        (ty -> Doc) ->
        (tm -> Doc) ->
        [Int] ->
        [Int] ->
        Tm ki ty tm ->
        Doc
      go prettyTyVar prettyTmVar tySupply tmSupply tm =
        case tm of
          TmVar a -> prettyTmVar a
          TmAnn a b ->
            Pretty.hsep
            [ (case a of
                 TmLamTm{} -> Pretty.parens
                 TmLamTy{} -> Pretty.parens
                 TmOpen{} -> Pretty.parens
                 _ -> id)
              (go prettyTyVar prettyTmVar tySupply tmSupply a)
            , Pretty.char ':'
            , prettyTy prettyTyVar tySupply b
            ]
          TmLamTm a b ->
            case tmSupply of
              [] -> undefined
              name : supply' ->
                let
                  var = Pretty.char 'x' <> Pretty.int name
                in
                  Pretty.char 'λ' <>
                  Pretty.parens
                    (Pretty.hsep
                     [ var
                     , Pretty.char ':'
                     , prettyTy prettyTyVar tySupply a
                     ]) <>
                  Pretty.char '.' <> Pretty.space <>
                  go
                    prettyTyVar (unvar (const var) prettyTmVar)
                    tySupply supply'
                    (fromBiscopeR b)
          TmLamTy a b ->
            case tySupply of
              [] -> undefined
              name : supply' ->
                let
                  var = Pretty.char 't' <> Pretty.int name
                in
                  Pretty.char 'Λ' <>
                  Pretty.parens
                    (Pretty.hsep
                     [ var
                     , Pretty.char ':'
                     , pretty a
                     ]) <>
                  Pretty.char '.' <> Pretty.space <>
                  go
                    (unvar (const var) prettyTyVar) prettyTmVar
                    supply' tmSupply
                    (fromBiscopeL b)
          TmAppTm a b ->
            Pretty.hsep
            [ (case b of
                 TmLamTm{} -> Pretty.parens
                 TmLamTy{} -> Pretty.parens
                 TmOpen{} -> Pretty.parens
                 _ -> id)
              (go prettyTyVar prettyTmVar tySupply tmSupply a)
            , (case b of
                 TmLamTm{} -> Pretty.parens
                 TmLamTy{} -> Pretty.parens
                 TmAppTm{} -> Pretty.parens
                 TmAppTy{} -> Pretty.parens
                 TmOpen{} -> Pretty.parens
                 _ -> id)
              (go prettyTyVar prettyTmVar tySupply tmSupply b)
            ]
          TmAppTy a b ->
            Pretty.hsep
            [ (case a of
                 TmLamTm{} -> Pretty.parens
                 TmLamTy{} -> Pretty.parens
                 TmOpen{} -> Pretty.parens
                 _ -> id)
              (go prettyTyVar prettyTmVar tySupply tmSupply a)
            , (case b of
                 TyForall{} -> Pretty.parens
                 TyExists{} -> Pretty.parens
                 TyApp{} -> Pretty.parens
                 _ -> id)
              (prettyTy prettyTyVar tySupply b)
            ]
          TmPack a b ->
            Pretty.braces $
            prettyTy prettyTyVar tySupply a <>
            Pretty.char ',' <> Pretty.space <>
            go prettyTyVar prettyTmVar tySupply tmSupply b
          TmOpen a b ->
            case (tySupply, tmSupply) of
              (tyName : tySupply', tmName : tmSupply') ->
                let
                  tyVar = Pretty.char 't' <> Pretty.int tyName
                  tmVar = Pretty.char 'x' <> Pretty.int tmName
                in
                  Pretty.hsep
                  [ Pretty.text "open"
                  , Pretty.parens $
                    tyVar <> Pretty.comma <> Pretty.space <> tmVar
                  , Pretty.char '='
                  , (case a of
                       TmOpen{} -> Pretty.parens
                       _ -> id)
                    (go prettyTyVar prettyTmVar tySupply tmSupply a)
                  , Pretty.text "in"
                  , go
                      (unvar (const tyVar) prettyTyVar)
                      (unvar (const tmVar) prettyTmVar)
                      tySupply'
                      tmSupply'
                      (fromBiscope2 b)
                  ]
              _ -> undefined

instance (Eq ki, Eq ty, Eq tm) => Eq (Tm ki ty tm) where
  (==) = eq2

instance (Show ki, Show ty, Show tm) => Show (Tm ki ty tm) where
  showsPrec = showsPrec2

instance Bifunctor (Tm ki) where; bimap = bisubstBimapDefault
instance Bisubst (Tm ki) (Ty ki) where
  bireturn = TmVar

  bisubst f g tm =
    case tm of
      TmVar a -> g a
      TmAnn a b -> TmAnn (bisubst f g a) (b >>= f)
      TmLamTm a b -> TmLamTm (a >>= f) (bisubstBiscopeR f g b)
      TmAppTm a b -> TmAppTm (bisubst f g a) (bisubst f g b)
      TmLamTy a b -> TmLamTy a $ bisubstBiscopeL f g b
      TmAppTy a b -> TmAppTy (bisubst f g a) (b >>= f)
      TmPack a b -> TmPack (a >>= f) (bisubst f g b)
      TmOpen a b -> TmOpen (bisubst f g a) (bisubstBiscope2 f g b)
instance Applicative (Tm ki ty) where; pure = return; (<*>) = ap
instance Monad (Tm ki ty) where
  return = bireturn; (>>=) a f = bisubst pure f a

data TypeError ki ty tm
  = KindMismatch (Kind ki) (Kind ki)
  | ExpectedArrowKind (Kind ki)
  | TypeMismatch (Ty ki ty) (Ty ki ty)
  | ExpectedArrowType (Ty ki ty)
  | ExpectedForall (Ty ki ty)
  | ExpectedExists (Ty ki ty)
  | TypeNotInScope ty
  | CtorNotInScope String
  | TermNotInScope tm
  | ScopeEscape
  | TypeDeep (TypeError ki (Var () ty) tm)
  | TermDeep (TypeError ki ty (Var () tm))
  deriving (Eq, Show)

checkKind ::
  (Eq ki, Eq ty) =>
  (ty -> Maybe (Kind ki)) ->
  (String -> Maybe (Kind ki)) ->
  Ty ki ty ->
  Kind ki ->
  Either (TypeError ki ty tm) ()
checkKind tyCtx ctorCtx ty ki = do
  res <- inferKind tyCtx ctorCtx ty
  unless (res == ki) . Left $ KindMismatch ki res

inferKind ::
  (Eq ki, Eq ty) =>
  (ty -> Maybe (Kind ki)) ->
  (String -> Maybe (Kind ki)) ->
  Ty ki ty ->
  Either (TypeError ki ty tm) (Kind ki)
inferKind tyCtx ctorCtx ty =
  case ty of
    TyVar a -> maybe (Left $ TypeNotInScope a) Right $ tyCtx a
    TyApp a b -> do
      aK <- inferKind tyCtx ctorCtx a
      case aK of
        KindArr x y -> y <$ checkKind tyCtx ctorCtx b x
        _ -> Left $ ExpectedArrowKind aK
    TyForall a b ->
      bimap TypeDeep id $
      KindType <$
      checkKind
        (unvar (const $ Just a) tyCtx)
        ctorCtx
        (fromBiscopeR b)
        KindType
    TyExists a b ->
      bimap TypeDeep id $
      KindType <$
      checkKind
        (unvar (const $ Just a) tyCtx)
        ctorCtx
        (fromBiscopeR b)
        KindType
    TyArr -> pure $ KindArr KindType (KindArr KindType KindType)
    TyCtor a ->
      maybe (Left $ CtorNotInScope a) Right $ ctorCtx a

check ::
  (Eq ki, Eq ty, Eq tm) =>
  (ty -> Maybe (Kind ki)) ->
  (String -> Maybe (Kind ki)) ->
  (tm -> Maybe (Ty ki ty)) ->
  Tm ki ty tm ->
  Ty ki ty ->
  Either (TypeError ki ty tm) ()
check tyCtx ctorCtx tmCtx tm ty =
  case tm of
    TmPack a b ->
      case ty of
        TyExists x y ->
          checkKind tyCtx ctorCtx a x *>
          check tyCtx ctorCtx tmCtx b (inst1BiscopeR a y)
        _ -> Left $ ExpectedExists ty
    _ -> do
      res <- infer tyCtx ctorCtx tmCtx tm
      unless (res == ty) . Left $ TypeMismatch ty res

infer ::
  (Eq ki, Eq ty, Eq tm) =>
  (ty -> Maybe (Kind ki)) ->
  (String -> Maybe (Kind ki)) ->
  (tm -> Maybe (Ty ki ty)) ->
  Tm ki ty tm ->
  Either (TypeError ki ty tm) (Ty ki ty)
infer tyCtx ctorCtx tmCtx tm =
  case tm of
    TmVar a ->
      maybe (Left $ TermNotInScope a) Right $ tmCtx a
    TmAnn a b -> b <$ check tyCtx ctorCtx tmCtx a b
    TmAppTm a b -> do
      aTy <- infer tyCtx ctorCtx tmCtx a
      case aTy of
        TyApp (TyApp TyArr x) y -> y <$ check tyCtx ctorCtx tmCtx b x
        _ -> Left $ ExpectedArrowType aTy
    TmAppTy a b -> do
      aTy <- infer tyCtx ctorCtx tmCtx a
      case aTy of
        TyForall k y -> inst1BiscopeR b y <$ checkKind tyCtx ctorCtx b k
        _ -> Left $ ExpectedForall aTy
    TmLamTm a b -> do
      checkKind tyCtx ctorCtx a KindType
      bTy <-
        bimap TermDeep id $
        infer
          tyCtx
          ctorCtx
          (unvar (const $ Just a) tmCtx)
          (fromBiscopeR b)
      pure $ TyApp (TyApp TyArr a) bTy
    TmLamTy a b -> do
      bTy <-
        bimap TypeDeep id $
        infer
          (unvar (const $ Just a) tyCtx)
          ctorCtx
          (fmap (fmap F) . tmCtx)
          (fromBiscopeL b)
      pure $ TyForall a (toBiscopeR bTy)
    TmOpen a b -> do
      aTy <- infer tyCtx ctorCtx tmCtx a
      case aTy of
        TyExists x y -> do
          bTy <-
            bimap (TermDeep . TypeDeep) id $
            infer
              (unvar (const $ Just x) tyCtx)
              ctorCtx
              (unvar (const $ Just $ fromBiscopeR y) $ fmap (fmap F) . tmCtx)
              (fromBiscope2 b)
          traverse (unvar (const $ Left ScopeEscape) Right) bTy
        _ -> Left $ ExpectedExists aTy
    TmPack{} -> error "can't infer pack"

idTy :: Ty ki ty
idTy =
  TyForall KindType $ toBiscopeR $
  TyApp (TyApp TyArr (TyVar $ B ())) (TyVar $ B ())

id_ :: Tm ki ty tm
id_ =
  TmLamTy KindType $ toBiscopeL $
  TmLamTm (TyVar $ B ()) $ toBiscopeR $
  TmAnn (TmVar $ B ()) (TyVar $ B ())

topTy :: Ty ki ty
topTy =
  TyExists KindType $ toBiscopeR $
  TyVar (B ())

topId :: Tm ki ty tm
topId = TmPack idTy id_

main :: IO ()
main = do
  let r1 = id_ @() @() @()
  print r1
  print $ pretty r1

  let r2 = infer (const Nothing) (const Nothing) (const Nothing) (id_ @() @() @())
  print r2
  print $ pretty <$> r2

  let r3 = topTy @() @()
  print r3
  print $ pretty r3

  let r4 = topId @() @() @()
  print r4
  print $ pretty r4

  print $ check (const Nothing) (const Nothing) (const Nothing) r4 r3
