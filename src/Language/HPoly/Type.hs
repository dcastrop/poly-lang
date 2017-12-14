{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.HPoly.Type
( Poly (..)
, CTy
, Forall
, Val
) where

import Data.Kind
import Data.Type.Nat
import Data.Type.Fin
import qualified Type.Family.Nat as Nat

type Z = 'Nat.Z
type S = 'Nat.S

infixl 5 :@>
infixl 5 :<@
infixr 4 :->

-- @@FIXME@@ separate polynomials from type :-> otherwise this is wrong!
data Poly (ty :: *) (n :: Nat.N)
  where
    TUnit  :: Poly ty Z

    TPrim  :: ty
           -> Poly ty Z

    TK     :: CTy ty
           -> Poly ty n

    TId    :: Fin n
           -> Poly ty n

    TProd  :: Poly ty n
           -> Poly ty n
           -> Poly ty n

    TSum   :: Poly ty n
           -> Poly ty n
           -> Poly ty n

    TFix   :: Poly ty (S n)
           -> Poly ty n

    (:@>)  :: Poly ty (S n)
           -> Poly ty n
           -> Poly ty n

    (:<@)  :: Poly ty (S n)
           -> Poly ty Z
           -> Poly ty n

    (:->)  :: Poly ty n
           -> Poly ty n
           -> Poly ty n

data CTy (ty :: *)
  where
    CTy :: Nat n
        -> Poly ty n
        -> CTy ty

type family Forall (n :: Nat.N)
                   (t :: Poly ty n)
                   = (c :: CTy ty) | c -> n t where
  Forall (S n) t = 'CTy (NNat (S n)) t

type family Val (t :: Poly ty Z) = (c :: CTy ty) | c -> t where
  Val t = 'CTy 'Z_ t

-- Isn't this implemented somewhere else?
type family NNat (n :: Nat.N) = (c :: Nat n) | c -> n where
  NNat Z     = 'Z_
  NNat (S n) = 'S_ (NNat n)

