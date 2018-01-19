{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Language.Poly.Erasure
  ( Erasure (..)
  ) where

import Data.Singletons ( SingKind, DemoteRep )
import Language.Poly.Type

class Erasure t e | t -> e where
  erase :: forall ty (a :: Type ty). SingKind ty => t a -> e (DemoteRep ty)
