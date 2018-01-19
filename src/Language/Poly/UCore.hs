{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Poly.UCore
  ( Core (..)
  , Nat (..)
  ) where

import Data.Text.Prettyprint.Doc ( Pretty, pretty )
import Data.Text.Prettyprint.EDoc

import Language.Poly.Type

-- forall a. f a ~> g a
data Nat t ty
  = Nid
  | NK     (Core t ty)
  | Nfst
  | Nsnd
  | Nsplit (Nat t ty) (Nat t ty)
  | Ninl
  | Ninr
  | Ncase  (Nat t ty) (Nat t ty)

data Core t ty
  = Unit
  | Prim  (t ty)
  | Const (Core t ty)
  | Id
  | Comp  (Core t ty) (Core t ty)
  | Fst
  | Snd
  | Split (Core t ty) (Core t ty)
  | Inl
  | Inr
  | Case  (Core t ty) (Core t ty)
  | Fmap  (Poly ty)   (Core t ty)
  | Hfmap (Nat t ty)
  | In
  | Out
  | Rec   (Core t ty) (Nat t ty) (Core t ty)

--------------------------------------------------------------------------------
-- Pretty printing instances

instance (Pretty ty, Pretty (t ty)) => Pretty (Nat t ty) where
  pretty Nid = [ppr| "n_id" |]
  pretty (NK c) = [ppr| "n_k" + c |]
  pretty Nfst = [ppr| "n_fst" |]
  pretty Nsnd = [ppr| "n_snd" |]
  pretty (Nsplit n m) = [ppr| "(" > n + "&&" + m > ")" |]
  pretty Ninl = [ppr| "n_inl" |]
  pretty Ninr = [ppr| "n_inr" |]
  pretty (Ncase n m) = [ppr| "n_case" + "{" + n + "|" + m + "}" |]

instance (Pretty ty, Pretty (t ty)) => Pretty (Core t ty) where
  pretty Unit          = [ppr| "()" |]
  pretty (Prim p)      = [ppr| p |]
  pretty (Const x)     = [ppr| "K" + x |]
  pretty Id            = [ppr| "I" |]
  pretty (Comp f g)    = [ppr| f + "." + g |]
  pretty Fst           = [ppr| "fst" |]
  pretty Snd           = [ppr| "snd" |]
  pretty (Split f g)   = [ppr| "(" + f + "/\\" + g + ")"|]
  pretty Inl           = [ppr| "inl" |]
  pretty Inr           = [ppr| "inr" |]
  pretty (Case f g)    = [ppr| "case" + "{" + f + "|" + g + "}"|]
  pretty (Fmap p f)    = [ppr| "("> p > ")" + f |]
  pretty (Hfmap n)     = [ppr| "[" > n > "]" |]
  pretty In            = [ppr| "in" |]
  pretty Out           = [ppr| "out" |]
  pretty (Rec g n h)   =
    [ppr| "hylo" > "[" > n > "]" + "(" > g > ")" + "(" > h > ")" |]
