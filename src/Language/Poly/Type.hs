{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Poly.Type
( Poly (..)
, Sing (..)
, Type (..)
, (:@:)
, app
) where

import Data.Kind hiding ( Type )
import Data.Singletons

data Poly ty =
    PId
  | PK (Type ty)
  | PProd (Poly ty) (Poly ty)
  | PSum (Poly ty) (Poly ty)

data instance Sing (p :: Poly ty) where
  SPId :: Sing 'PId
  SPK  :: Sing t -> Sing ('PK t)
  SPProd :: Sing p1 -> Sing p2 -> Sing ('PProd p1 p2)
  SPSum :: Sing p1 -> Sing p2 -> Sing ('PSum p1 p2)

instance SingI 'PId where
  sing = SPId
instance SingI t => SingI ('PK t) where
  sing = SPK sing
instance (SingI p1, SingI p2) => SingI ('PProd p1 p2) where
  sing = SPProd sing sing
instance (SingI p1, SingI p2) => SingI ('PSum p1 p2) where
  sing = SPSum sing sing

instance SingKind ty => SingKind (Poly ty) where
  type DemoteRep (Poly ty) = Poly (DemoteRep ty)

  fromSing SPId = PId
  fromSing (SPK t) = PK (fromSing t)
  fromSing (SPProd p1 p2) = PProd (fromSing p1) (fromSing p2)
  fromSing (SPSum p1 p2) = PSum (fromSing p1) (fromSing p2)

  toSing PId = SomeSing SPId
  toSing (PK t) = case toSing t of
                    SomeSing k -> SomeSing (SPK k)
  toSing (PProd p1 p2) =
      case (toSing p1, toSing p2) of
        (SomeSing t1, SomeSing t2) -> SomeSing $ SPProd t1 t2
  toSing (PSum p1 p2) =
      case (toSing p1, toSing p2) of
          (SomeSing t1, SomeSing t2) -> SomeSing $ SPSum t1 t2

infixl 5 :@:
infixr 4 :->

data Type ty =
    TUnit
  | TPrim ty
  | TProd (Type ty) (Type ty)
  | TSum (Type ty) (Type ty)
  | TFix (Poly ty)
  | Type ty :-> Type ty

data instance Sing (t :: Type ty) where
  STUnit :: Sing 'TUnit
  STPrim :: Sing t  -> Sing ('TPrim t)
  STProd :: Sing t1 -> Sing t2 -> Sing ('TProd t1 t2)
  STSum  :: Sing t1 -> Sing t2 -> Sing ('TSum  t1 t2)
  STFix  :: Sing p  -> Sing ('TFix p)
  STArr  :: Sing t1 -> Sing t2 -> Sing (t1 ':-> t2)

instance SingI 'TUnit where
  sing = STUnit
instance SingI t => SingI ('TPrim t) where
  sing = STPrim sing
instance (SingI p1, SingI p2) => SingI ('TProd p1 p2) where
  sing = STProd sing sing
instance (SingI p1, SingI p2) => SingI ('TSum p1 p2) where
  sing = STSum sing sing
instance SingI p1 => SingI ('TFix p1) where
  sing = STFix sing
instance (SingI p1, SingI p2) => SingI (p1 ':-> p2) where
  sing = STArr sing sing

instance SingKind ty => SingKind (Type ty) where
  type DemoteRep (Type ty) = Type (DemoteRep ty)

  fromSing STUnit = TUnit
  fromSing (STPrim t) = TPrim $ fromSing t
  fromSing (STProd t1 t2) = TProd (fromSing t1) (fromSing t2)
  fromSing (STSum t1 t2) = TSum (fromSing t1) (fromSing t2)
  fromSing (STFix p) = TFix (fromSing p)
  fromSing (STArr t1 t2) = fromSing t1 :-> fromSing t2

  toSing TUnit = SomeSing STUnit
  toSing (TPrim (toSing -> SomeSing t)) = SomeSing $ STPrim t
  toSing (TProd (toSing -> SomeSing t1) (toSing -> SomeSing t2)) =
      SomeSing $ STProd t1 t2
  toSing (TSum (toSing -> SomeSing t1) (toSing -> SomeSing t2)) =
      SomeSing $ STSum t1 t2
  toSing (TFix (toSing -> SomeSing p)) = SomeSing $ STFix p
  toSing ((toSing -> SomeSing t1) :-> (toSing -> SomeSing t2)) =
      SomeSing $ STArr t1 t2

type family (:@:) (p :: Poly ty) (t :: Type ty) :: Type ty where
  'PK c :@: t = c
  'PId :@: t = t
  'PProd p1 p2 :@: t = 'TProd (p1 :@: t) (p2 :@: t)
  'PSum p1 p2 :@: t = 'TSum (p1 :@: t) (p2 :@: t)

app :: forall (ty :: *) (p :: Poly ty) (t :: Type ty). Sing p -> Sing t -> Sing (p :@: t)
app SPId           t = t
app (SPK c)       _t = c
app (SPProd p1 p2) t = STProd (p1 `app` t) (p2 `app` t)
app (SPSum p1 p2)  t = STSum  (p1 `app` t) (p2 `app` t)
