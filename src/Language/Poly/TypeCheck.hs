{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Language.Poly.TypeCheck
  ( TC(..)
  , Typed(..)
  , TcError(..)
  ) where

import Control.Monad.Except ( MonadError(..) )
import Data.Kind hiding ( Type )
import Data.Singletons ( Sing, DemoteRep )

import Language.Poly.Type

data TcError =
  TcError

infix 4 :::
data Typed ty (t :: Type ty -> *)
  where
    (:::) :: forall ty (a :: Type ty) (t :: Type ty -> *).
             t a -> Sing a -> Typed ty t

class TC t u | t -> u where
  typeCheck :: MonadError TcError m => u (DemoteRep ty) -> m (Typed ty t)
