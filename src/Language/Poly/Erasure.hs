{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Language.Poly.Erasure
  ( Erasure (..)
  ) where

import Data.Kind hiding ( Type )

import Data.Singletons ( SingKind, DemoteRep )
import Language.Poly.Type

class SingKind ty => Erasure ty (t :: Type ty -> *) e | ty t -> e where
  erase :: t a -> e (DemoteRep ty)
