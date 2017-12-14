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
, Sem(..)
) where

import Control.Arrow ( (&&&) )
import qualified Data.Kind as Kind
import qualified Data.Functor.Sum as Functor
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Const as Functor
import qualified Data.Functor.Identity as Functor
import Data.Proxy ( Proxy(..) )

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

pmap :: SPoly p -> (a -> b) -> App p a -> App p b
pmap FK{} _f = id
pmap FId f = f
pmap (FProd p1 p2) f = (pmap p1 f . fst) &&& (pmap p2 f . snd)
pmap (FSum p1 p2) f = either (Left . pmap p1 f) (Right . pmap p2 f)

wrap :: SPoly p
     -> forall a.
          Proxy a -> App p (InterpTy a) -> InterpTy (p :@: a)
wrap FK{} _ = id
wrap FId{} _ = id
wrap (FProd p1 p2) a = (wrap p1 a . fst) &&& (wrap p2 a . snd)
wrap (FSum p1 p2) a = either (Left . wrap p1 a) (Right . wrap p2 a)

unwrap :: SPoly p
       -> forall a.
            Proxy a -> InterpTy (p :@: a) -> App p (InterpTy a)
unwrap FK{} _ = id
unwrap FId{} _ = id
unwrap (FProd p1 p2) a = (unwrap p1 a . fst) &&& (unwrap p2 a . snd)
unwrap (FSum p1 p2) a = either (Left . unwrap p1 a) (Right . unwrap p2 a)

wrapp :: SPoly p
      -> forall a. Proxy a -> InterpF p (InterpTy a) -> InterpTy (p :@: a)
wrapp FK{} _a = Functor.getConst
wrapp FId{} _a = Functor.runIdentity
wrapp (FProd p1 p2) a = (wrapp p1 a . fst &&& wrapp p2 a . snd) . unProd
  where
    unProd (Functor.Pair l r) = (l, r)
wrapp (FSum p1 p2) a = either (Left . wrapp p1 a) (Right . wrapp p2 a) . unSum
  where
    unSum (Functor.InL x) = Left x
    unSum (Functor.InR x) = Right x

unwrapp :: SPoly p -> Proxy a -> InterpTy (p :@: a) -> InterpF p (InterpTy a)
unwrapp FK{} _a = Functor.Const
unwrapp FId{} _a = Functor.Identity
unwrapp (FProd p1 p2) a =
    uncurry Functor.Pair . (unwrapp p1 a . fst &&& unwrapp p2 a . snd)
unwrapp (FSum p1 p2) a =
    either (Functor.InL . unwrapp p1 a) (Functor.InR . unwrapp p2 a)

class SemTy t => Sem (f :: Type t -> *) where
  eval :: f ty -> InterpTy ty

instance Sem f => Sem (Core f) where
  eval Unit = ()
  eval (Prim p) = eval p
  eval (Const x) = const (eval x)
  eval Id = id
  eval (Comp x1 x2) = eval x1 . eval x2
  eval Fst = fst
  eval Snd = snd
  eval (Split x1 x2) = eval x1 &&& eval x2
  eval Inl = Left
  eval Inr = Right
  eval (Case x1 x2) = eval x1 `either` eval x2
  eval (Fmap p f) = wrap p (cod (typeOf f))
                      . pmap p (eval f)
                      . unwrap p (dom (typeOf f))
  eval (Hfmap p x) = evalNat p x
  eval t@In  = FIn . unwrapp (tyFix $ cod $ typeOf t) (cod (typeOf t))
  eval t@Out = wrapp (tyFix $ dom $ typeOf t) (dom (typeOf t)) . fOut
  eval f@(Rec g m h) =
    eval g .
    evalNat m (cod (typeOf f)).
    wrap (ntfrom m) (cod (typeOf f)) .
    pmap (ntfrom m) (eval f) .
    unwrap (ntfrom m) (dom (typeOf f)) .
    eval h

evalNat :: Sem t => Nat t p q
        -> forall a. Proxy a -> InterpTy (p :@: a) -> InterpTy (q :@: a)
evalNat Nid _ = id
evalNat (NK f) _ = eval f
evalNat Nfst _ = fst
evalNat Nsnd _ = snd
evalNat Ninl _ = Left
evalNat Ninr _ = Right
evalNat (Nsplit x1 x2) a = evalNat x1 a &&& evalNat x2 a
evalNat (Ncase x1 x2) a = evalNat x1 a `either` evalNat x2 a

typeOf :: Core t a -> Proxy a
typeOf _ = Proxy

tyFix :: IsPoly f => Proxy ('TFix f) -> SPoly f
tyFix _ = spoly

dom :: Proxy (a ':-> b) -> Proxy a
dom _ = Proxy

cod :: Proxy (a ':-> b) -> Proxy b
cod _ = Proxy

ntfrom :: IsPoly f => Nat a f g -> SPoly f
ntfrom _ = spoly
