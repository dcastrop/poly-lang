{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Poly.Interp
  ( SemTy(..)
  , SemF(..)
  , AppF(..)
  , typeOf
  , dom
  , cod
  , tyLeft
  , tyRight
  , tfix
  , Sem (..)
) where

import Control.Arrow ( (&&&) )
import qualified Data.Kind as Kind
import qualified Data.Functor.Sum as Functor
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Const as Functor
import qualified Data.Functor.Identity as Functor
import Data.Singletons ( SingI (..), Sing )

import Language.Poly.Type
import Language.Poly.Core

class SemF f where
  type InterpF (p :: f) :: * -> *

class AppF f k where
  type App (p :: f) (h :: k) :: k

class SemTy ty where
  type InterpTy (t :: ty) :: *

instance SemTy ty => SemF (Poly ty) where
  type InterpF ('PK t) = Functor.Const (InterpTy t)
  type InterpF 'PId = Functor.Identity
  type InterpF ('PSum f g) = Functor.Sum (InterpF f) (InterpF g)
  type InterpF ('PProd f g) = Functor.Product (InterpF f) (InterpF g)

instance SemTy ty => AppF (Poly ty) Kind.Type where
  type App ('PK t) h = InterpTy t
  type App 'PId h = h
  type App ('PSum f g) h = Either (App f h) (App g h)
  type App ('PProd f g) h = (App f h, App g h)

instance SemTy ty => AppF (Poly ty) (Type ty) where
  type App ('PK t) h = t
  type App 'PId h = h
  type App ('PSum f g) h = 'TSum (App f h) (App g h)
  type App ('PProd f g) h = 'TProd (App f h) (App g h)

newtype Fix f = FIn { fOut :: f (Fix f) }

instance SemTy ty => SemTy (Type ty) where
  type InterpTy 'TUnit = ()
  type InterpTy ('TPrim t) = InterpTy t
  type InterpTy ('TProd a b) = (InterpTy a, InterpTy b)
  type InterpTy ('TSum a b) = Either (InterpTy a) (InterpTy b)
  type InterpTy ('TFix p) = Fix (InterpF p)
  type InterpTy (a ':-> b) = InterpTy a -> InterpTy b

pmap :: forall a b (p :: Poly ty). Sing p -> (a -> b) -> App p a -> App p b
pmap SPK{} _f = id
pmap SPId   f = f
pmap (SPProd p1 p2) f = (pmap p1 f . fst) &&& (pmap p2 f . snd)
pmap (SPSum  p1 p2) f = either (Left . pmap p1 f) (Right . pmap p2 f)

wrap :: forall (p :: Poly ty). Sing p
     -> forall a.
          Sing a -> App p (InterpTy a) -> InterpTy (p :@: a)
wrap SPK{} _ = id
wrap SPId{} _ = id
wrap (SPProd p1 p2) a = (wrap p1 a . fst) &&& (wrap p2 a . snd)
wrap (SPSum p1 p2) a = either (Left . wrap p1 a) (Right . wrap p2 a)

unwrap :: forall (p :: Poly ty). Sing p
       -> forall a.
            Sing a -> InterpTy (p :@: a) -> App p (InterpTy a)
unwrap SPK{} _ = id
unwrap SPId{} _ = id
unwrap (SPProd p1 p2) a = (unwrap p1 a . fst) &&& (unwrap p2 a . snd)
unwrap (SPSum p1 p2) a = either (Left . unwrap p1 a) (Right . unwrap p2 a)

wrapp :: forall (p :: Poly ty). Sing p
      -> forall a. Sing a -> InterpF p (InterpTy a) -> InterpTy (p :@: a)
wrapp SPK{} _a = Functor.getConst
wrapp SPId{} _a = Functor.runIdentity
wrapp (SPProd p1 p2) a = (wrapp p1 a . fst &&& wrapp p2 a . snd) . unProd
  where
    unProd (Functor.Pair l r) = (l, r)
wrapp (SPSum p1 p2) a = either (Left . wrapp p1 a) (Right . wrapp p2 a) . unSum
  where
    unSum (Functor.InL x) = Left x
    unSum (Functor.InR x) = Right x

unwrapp :: forall (p :: Poly ty). Sing p -> forall a.
              Sing a -> InterpTy (p :@: a) -> InterpF p (InterpTy a)
unwrapp SPK{} _a = Functor.Const
unwrapp SPId{} _a = Functor.Identity
unwrapp (SPProd p1 p2) a =
    uncurry Functor.Pair . (unwrapp p1 a . fst &&& unwrapp p2 a . snd)
unwrapp (SPSum p1 p2) a =
    either (Functor.InL . unwrapp p1 a) (Functor.InR . unwrapp p2 a)

class SemTy t => Sem (f :: Type t -> *) where
  evalTy :: forall (ty :: Type t). Sing ty -> f ty -> InterpTy ty
  eval :: forall (ty :: Type t). SingI ty => f ty -> InterpTy ty
  eval = evalTy sing

instance Sem f => Sem (Core f) where
  evalTy _ Unit = ()
  evalTy _ (Prim p) = evalTy sing p
  evalTy _ (Const x) = const (evalTy sing x)
  evalTy _ Id = id
  evalTy _ Fst = fst
  evalTy _ Snd = snd
  evalTy _ (Split x1 x2) = eval x1 &&& eval x2
  evalTy _ Inl = Left
  evalTy _ Inr = Right
  evalTy _ (Case x1 x2) = eval x1 `either` eval x2
  evalTy _ (Fmap p f) = wrap p (cod (typeOf f))
                    . pmap p (eval f)
                    . unwrap p (dom (typeOf f))
  evalTy _ (Hfmap p x) = evalNat p x
  evalTy ty   In  = FIn . unwrapp (tfix $ cod ty) (cod ty)
  evalTy ty   Out = wrapp (tfix $ dom ty) (dom ty) . fOut
  evalTy ty f@(Rec g m h) =
    evalTy (app (ntto m) (cod ty) `STArr` cod ty) g .
    evalNat m (cod ty).
    wrap (ntfrom m) (cod ty) .
    pmap (ntfrom m) (evalTy ty f) .
    unwrap (ntfrom m) (dom ty) .
    evalTy (dom ty `STArr` app (ntfrom m) (dom ty)) h
  evalTy _ (Comp x1 x2) = eval x1 . eval x2
  evalTy _ (Curry _) = error "Unimplemented"
  evalTy _ (Ap _) = error "Unimplemented"

evalNat :: (Sem t, SingI p, SingI q)
        => Nat t p q
        -> forall a. Sing a -> InterpTy (p :@: a) -> InterpTy (q :@: a)
evalNat Nid _ = id
evalNat (NK f) _ = eval f
evalNat Nfst _ = fst
evalNat Nsnd _ = snd
evalNat Ninl _ = Left
evalNat Ninr _ = Right
evalNat (Nsplit x1 x2) a = evalNat x1 a &&& evalNat x2 a
evalNat (Ncase x1 x2) a = evalNat x1 a `either` evalNat x2 a

typeOf :: SingI a => Core t a -> Sing a
typeOf _ = sing

tfix :: forall (f :: Poly ty). Sing ('TFix f) -> Sing f
tfix (STFix t) = t

dom :: Sing (a ':-> b) -> Sing a
dom (t1 `STArr` _t2) = t1

cod :: Sing (a ':-> b) -> Sing b
cod (_t1 `STArr` t2) = t2

tyLeft  :: Sing (a '`TSum` b) -> Sing a
tyLeft (t1 `STSum` _t2) = t1

tyRight :: Sing (a '`TSum` b) -> Sing b
tyRight (_t1 `STSum` t2) = t2

ntfrom :: SingI f => Nat a f g -> Sing f
ntfrom _ = sing

ntto :: SingI g => Nat a f g -> Sing g
ntto _ = sing
