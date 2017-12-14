{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Language.Poly.Type
( Poly (..)
, SPoly (..)
, IsPoly (..)
, Type (..)
, (:@:)
) where

import Data.Proxy ( Proxy(..) )

data Poly ty =
    PId
  | PK (Type ty)
  | PProd (Poly ty) (Poly ty)
  | PSum (Poly ty) (Poly ty)

data SPoly (p :: Poly ty)
  where
    FK     :: Proxy ty
           -> SPoly ('PK ty)

    FId    :: SPoly 'PId

    FProd  :: SPoly f
           -> SPoly g
           -> SPoly ('PProd f g)

    FSum   :: SPoly f
           -> SPoly g
           -> SPoly ('PSum f g)

class IsPoly (a :: Poly ty) where
  spoly :: SPoly a
instance IsPoly ('PK t) where
  spoly = FK Proxy
instance IsPoly 'PId where
  spoly = FId
instance (IsPoly f, IsPoly g) => IsPoly ('PProd f g) where
  spoly = FProd spoly spoly
instance (IsPoly f, IsPoly g) => IsPoly ('PSum f g) where
  spoly = FSum spoly spoly

infixl 5 :@:
infixr 4 :->

data Type ty =
    TUnit
  | TPrim ty
  | TProd (Type ty) (Type ty)
  | TSum (Type ty) (Type ty)
  | TFix (Poly ty)
  | Type ty :-> Type ty

type family (:@:) (p :: Poly ty) (t :: Type ty) :: Type ty where
  'PK c :@: t = c
  'PId :@: t = t
  'PProd p1 p2 :@: t = 'TProd (p1 :@: t) (p2 :@: t)
  'PSum p1 p2 :@: t = 'TSum (p1 :@: t) (p2 :@: t)

