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
import Data.Singletons ( Sing, SingI, Demote )

import Language.Poly.Type

data TcError =
  TcError

infix 3 :::
data Typed (t :: Type ty -> *)
  where
    (:::) :: SingI a => t a -> Sing a -> Typed t

class TC (t :: Type ty -> *) u | t -> u where
  typeCheck :: MonadError TcError m => u (Demote ty) -> m (Typed t)
