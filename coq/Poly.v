(** Delay monad ****************************************************************)

CoInductive Delay (t : Type) : Type :=
| Now  : t -> Delay t
| Wait : Delay t -> Delay t.
Arguments Now {t} v.
Arguments Wait {t} d.

CoFixpoint bot {X} : Delay X :=
  Wait bot.

Definition peek {A} (x : Delay A) : Delay A :=
  match x with
  | Now v => Now v
  | Wait y => Wait y
  end.

Theorem peekThm : forall A (x : Delay A), x = peek x.
Proof.
  destruct x; reflexivity.
Qed.

(* Either both terminate in the same number of steps, or both diverge *)
CoInductive sim A : Delay A -> Delay A -> Prop :=
| ENow   : forall v, sim A (Now v) (Now v)
| EWait : forall w1 w2, sim A w1 w2 -> sim A (Wait w1) (Wait w2).

Inductive eval A : Delay A -> A -> Prop :=
| eNow  : forall x, eval A (Now x) x
| eWait : forall w x, eval A w x -> eval A (Wait w) x.
Arguments eNow {_}.
Arguments eWait {_ _ _}.

Definition approxEq A (d1 d2: Delay A) : Prop :=
  forall (v : A), eval A d1 v <-> eval A d2 v.

CoFixpoint bind {A B} (x : Delay A) : (forall (v : A), eval A x v -> Delay B) -> Delay B :=
  match x return (forall (v : A), eval A x v -> Delay B) -> Delay B with
  | Now v => fun f => f v (eNow v)
  | Wait w => fun f => Wait (bind w (fun v' p' => f v' (eWait p')))
  end.
Arguments bind {_ _}.

CoFixpoint join {A} (x : Delay (Delay A)) : Delay A :=
  match x with
  | Now v => v
  | Wait w => Wait (join w)
  end.

Notation "m >>= f" := (bind m f) (at level 42, left associativity).
Notation "m1 >> m2" := (bind m1 (fun _ => m2)) (at level 42, left associativity).
Definition mret t (x : t) := Now x.
Arguments mret {t} x.

Definition fwait {A B} (w : Delay A)
           (f : forall (y : A), eval A (Wait w) y -> Delay B)
           (y : A) (w : eval A w y) : Delay B :=
  f y (eWait w).

Lemma evalBind :
  forall A B (x : A) (y : B)
    (m : Delay A) (f : forall (x : A), eval A m x -> Delay B)
    (pr0 : eval A m x) (pr1 : eval B (m >>= f) y),
    eval B (f x pr0) y.
Proof.
  fix IH 7.
  intros A B x y m f pr0 pr1.
  rewrite (peekThm _ (_ >>= _)) in pr1.
  destruct pr0.
  - rewrite (peekThm _ (f _ _)); trivial.
  - simpl in *; inversion pr1; subst.
    apply (IH _ _ _ y w (fwait w f) pr0 H0).
Qed.
Arguments evalBind {_ _ _ _ _ _}.

Lemma evalNow : forall A (x y : A), eval A (Now x) y -> y = x.
Proof.
  intros A x y pr; inversion pr; reflexivity.
Qed.
Arguments evalNow {_ _ _}.

Notation "A ~> B" := (A -> Delay B) (at level 99, right associativity).

(** Recursive types ************************************************************)

Inductive functor : Type :=
| pid    : functor
| pconst : Set -> functor
| pprod  : functor -> functor -> functor
| psum   : functor -> functor -> functor
| pexp   : Set -> functor -> functor.

Fixpoint comp (P1 : functor) (P2 : functor) : functor :=
  match P1 with
  | pid => P2
  | pconst Y => pconst Y
  | pprod P11 P12 => pprod (comp P11 P2) (comp P12 P2)
  | psum P11 P12 => psum (comp P11 P2) (comp P12 P2)
  | pexp D P1 => pexp D (comp P1 P2)
  end.
Fixpoint Exp P (n : nat) : functor :=
  match n with
  | O => pid
  | S m => comp P (Exp P m)
  end.
Notation " P ^ n " := (Exp P n) (at level 30, right associativity).

Notation " \PI " := (pid) (at level 0) : functor_scope.
Notation " \PK{ X }" := (pconst X) (at level 0) : functor_scope.
Notation " l \PP r " := (pprod l r) (at level 40, left associativity) : functor_scope.
Notation " l \PS r " := (psum l r) (at level 50, left associativity) : functor_scope.

(** Recursive types + delay ****************************************************)

Fixpoint app (P : functor) (A : Set) : Set :=
  match P with
  | pid => A
  | pconst X => X
  | pprod P1 P2 => app P1 A * app P2 A
  | psum P1 P2 => app P1 A + app P2 A
  | pexp D P1 => D ~> app P1 A
  end.

Fixpoint map {A B : Set} (P : functor) (f : A -> B) : app P A -> app P B :=
  match P return app P A -> app P B with
  | pid => fun x => f x
  | pconst _ => fun y => y
  | pprod P1 P2 => fun x => (map P1 f (fst x), map P2 f (snd x))
  | psum P1 P2 => fun x => match x with
                       | inl y => inl (map P1 f y)
                       | inr y => inr (map P2 f y)
                   end
  | pexp D P => fun g r => g r >>= fun v _ => mret (map P f v)
  end.

Fixpoint waitF {A : Set} (F : functor) : app F (Delay A) ~> app F A :=
  match F return app F (Delay A) -> Delay (app F A) with
  | pid => fun x => x
  | pconst _ => fun y => mret y
  | pprod P1 P2 => fun x => waitF P1 (fst x) >>=
                              fun l _ => waitF P2 (snd x) >>=
                                            fun r _ => mret (l, r)
  | psum P1 P2 => fun x => match x with
                       | inl y => waitF P1 y >>= fun v _ => mret (inl v)
                       | inr y => waitF P2 y >>= fun v _ => mret (inr v)
                       end
  | pexp D P => fun g => mret (fun r => g r >>= fun v _ => waitF P v)
  end.

Definition fmap {A B : Set} (P : functor) (f : A ~> B) : app P A ~> app P B :=
  fun x => waitF P (map P f x).

Definition pshape (P : functor) : Set := app P unit.

Inductive posExp (D : Set) (p : functor) (f : D ~> pshape p)
          (pos : pshape p -> Set) : Set :=
| PExp : forall (d : D) (v : pshape p),
    eval _ (f d) v -> pos v -> posExp D p f pos.
Arguments PExp {_ _ _ _}.

Definition valueOfPos {D p f pos} (x : posExp D p f pos) : D :=
  match x with
  | PExp d _ _ _ => d
  end.

Definition shapeOfPos {D p f pos} (x : posExp D p f pos) : pshape p :=
  match x with
  | PExp _ v _ _ => v
  end.

Definition evalOfPos {D p f pos} (x : posExp D p f pos)
  : eval (pshape p) (f (valueOfPos x)) (shapeOfPos x) :=
  match x with
  | PExp _ _ p _ => p
  end.

Definition nextPos {D p f pos} (x : posExp D p f pos) : pos (shapeOfPos x) :=
  match x with
  | PExp _ _ _ s => s
  end.

Definition shape {X} (P : functor) (x : app P X) : pshape P :=
  map P (fun _ => tt) x.

Fixpoint pos (p : functor) : pshape p -> Set :=
  match p return app p unit -> Set with
  | pid          => fun _ => unit
  | pconst x     => fun _ => Empty_set
  | pprod  P1 P2 => fun s => pos P1 (fst s) + pos P2 (snd s)
  | psum   P1 P2 => fun s => match s with
                         | inl s' => pos P1 s'
                         | inr s' => pos P2 s'
                         end
  | pexp  D P1   => fun s => posExp D P1 s (pos P1)
  end %type.

CoInductive App (P : functor) (X : Set) : Set :=
| AppC : forall (s : pshape P), (pos P s ~> X) -> App P X.
Arguments AppC {_ _}.

Definition pmap {X Y : Set} P (f : X -> Y) (v : App P X) : App P Y :=
  match v with
  | AppC s g => AppC s (fun s => g s >>= fun v _ => mret (f v))
  end.

Definition pshapeOf {X} P (x : App P X) : pshape P :=
  match x with
  | AppC s _ => s
  end.

Definition posOf {X} P (x : App P X) : pos P (pshapeOf P x) ~> X :=
  match x return pos P (pshapeOf P x) ~> X with
  | AppC _ p => p
  end.

Definition castShape {P1} {v0 v1 : pshape P1} (eq : v0 = v1)
  : pos P1 v0 -> pos P1 v1 :=
  match eq in (_ = v1) return pos P1 v0 -> pos P1 v1 with
  | eq_refl => fun x => x
  end.

Fixpoint fromApp_ {X : Set} P : forall (s : pshape P), (pos P s ~> X) ~> app P X :=
  match P return forall (s : pshape P), (pos P s ~> X) ~> app P X with
  | pid => fun s f => f tt
  | pconst _ => fun s f => mret s
  | pprod P1 P2 =>
    fun s f => fromApp_ P1 (fst s) (fun i => f (inl i)) >>=
                    fun lv _ => fromApp_ P2 (snd s) (fun i => f (inr i)) >>=
                                   fun rv _ => mret (lv, rv)
  | psum P1 P2 =>
    fun s => match s with
          | inl s' => fun f => fromApp_ P1 s' f >>= fun rv _ => mret (inl rv)
          | inr s' => fun f => fromApp_ P2 s' f >>= fun rv _ => mret (inr rv)
          end
  | pexp D P1 =>
    fun s f => mret (fun d => s d >>= fun r p => fromApp_ P1 r (fun i => f (PExp d r p i)))
  end.

Definition fromApp {X : Set} P (v : App P X) : Delay (app P X) :=
  fromApp_ P (pshapeOf P v) (posOf P v).

Fixpoint toApp {X : Set} P : app P X -> App P X :=
  match P return app P X -> App P X with
  | pid          => fun x => @AppC pid        X tt (fun _ => mret x)
  | pconst A     => fun x => @AppC (pconst A) X x  (fun e => match e with end)
  | pprod  P1 P2 =>
    fun x => match x with
          | (l, r) =>
            match toApp P1 l, toApp P2 r with
            | AppC xl fl, AppC xr fr =>
              @AppC (pprod P1 P2) X
                    (xl, xr)
                    (fun e => match e with
                           | inl e' => fl e'
                           | inr e' => fr e'
                           end)
            end
          end
  | psum   P1 P2 =>
    fun x => match x with
          | inl y => match toApp P1 y with
                    | AppC xy fy => @AppC (psum P1 P2) X (inl xy) fy
                    end
          | inr y => match toApp P2 y with
                    | AppC xy fy => @AppC (psum P1 P2) X (inr xy) fy
                    end
          end
  | pexp   D  P1 =>
    fun x => @AppC (pexp D P1) X
                (fun d => x d >>= fun v _ => mret (pshapeOf P1 (toApp P1 v)))
                (fun p => x (valueOfPos p)
                         >>= fun v1 pr1 =>
                               posOf P1
                                     (toApp P1 v1)
                                     (castShape
                                        (evalNow (evalBind pr1 (evalOfPos p)))
                                        (nextPos p)))
  end.

Inductive Mu (P : functor) : Set :=
| MuI : App P (Mu P) -> Mu P.
Arguments MuI {_}.

Definition MuO P (x : Mu P) : App P (Mu P) :=
  match x with
  | MuI y => y
  end.

Definition iin  P (x : app P (Mu P)) : Mu P := MuI (toApp P x).
Definition iout P (x : Mu P) : Delay (app P (Mu P)) :=
  match x with
  | MuI z => fromApp P z
  end.

CoInductive Nu (P : functor) : Set :=
| NuI : App P (Nu P) -> Nu P.
Arguments NuI {_}.

Definition NuO P (x : Mu P) : App P (Mu P) :=
  match x with
  | MuI y => y
  end.

Definition cin  P (x : app P (Nu P)) : Nu P := NuI (toApp P x).
Definition cout P (x : Nu P) : Delay (app P (Nu P)) :=
  match x with
  | NuI z => fromApp P z
  end.

Lemma app_comp : forall P1 P2 X, app (comp P1 P2) X = app P1 (app P2 X).
Proof.
  induction P1; intros P2 X; simpl;
    try rewrite IHP1_1, IHP1_2; try rewrite IHP1; auto.
Defined.

Lemma exp_S : forall X P n, app P (app (P ^ n) X) = app (P ^ (S n)) X.
Proof.
  intros X P n; revert X; induction P; intros X; simpl;
    repeat rewrite app_comp; auto.
Defined.

Definition castDelay {A B : Set} (pr : A = B) (x : Delay A) : Delay B :=
  match pr in _ = B return Delay A -> Delay B with
  | eq_refl => fun x => x
  end x.


Fixpoint unroll (n : nat) P (x : Nu P) : Delay (app (P^n) (Nu P)) :=
  match n return Delay (app (P^n) (Nu P)) with
  | O => mret x
  | S m => cout P x >>= fun v _ => castDelay
                                 (exp_S (Nu P) P m)
                                 (fmap P (unroll m P) v)
  end.

Definition take (n : nat) P (x : Nu P) : Delay (app (P^n) unit) :=
  join (unroll n P x >>= fun v _ => mret (fmap (P^n) (fun _ => mret tt) v)).

Fixpoint tryUnwrap {A} (fuel : nat) (d : Delay A) : option A :=
  match fuel with
  | O => None
  | S m => match d with
          | Now v => Some v
          | Wait w => tryUnwrap m w
          end
  end.

Definition large := 1.

Fixpoint tryTake (n : nat) P (x : Nu P) : option (app (P^n) unit) :=
  tryUnwrap large (take n P x).

Fail CoFixpoint coindToInd P (x : Nu P) : Delay (Mu P) :=
  cout P x >>= fun px _ => fmap P (fun dx => dx >>= fun x _ => coindToInd P x) px >>= fun r _ => mret (iin P r).

Fixpoint unrollI (n : nat) P (x : Mu P) : Delay (app (P^n) (Mu P)) :=
  match n return Delay (app (P^n) (Mu P)) with
  | O => Now x
  | S m => castDelay
            (exp_S _ P m)
            (iout P x >>= fun v _ => fmap P (unrollI m P) v)
  end.

Definition takeI (n : nat) P (x : Mu P) : Delay (app (P^n) unit) :=
  join (unrollI n P x >>= fun v _ => mret (fmap (P^n) (fun _ => mret tt) v)).

Fixpoint tryTakeI (n : nat) P (x : Mu P) : option (app (P^n) unit) :=
  tryUnwrap large (takeI n P x).

CoFixpoint foldP {A} P (f : app P A ~> A) (x : Mu P) : Delay A :=
  iout P x >>= fun r _ => fmap P (foldP P f) r >>= fun v _ => f v.

Section ExamplesRec.
  Open Scope functor_scope.

  Definition natP : functor := \PK{unit} \PS \PI.

  Definition listP (A : Set) : functor := \PK{unit} \PS \PK{ A } \PP \PI.
  Definition CoList A := Nu (listP A).
  Definition List A := Mu (listP A).

  CoFixpoint build0 (n : nat) : CoList nat :=
    cin (listP nat) (inr (n, build0 (S n))).

  Fixpoint buildI0 (n : nat) (m : nat) : List nat :=
    match n with
    | O => iin (listP nat) (inl tt)
    | S n' => iin (listP nat) (inr (m, buildI0 n' (S m)))
    end.

  Eval compute in tryTake 20 (listP nat) (build0 3).
  Eval compute in tryTakeI 20 (listP nat) (buildI0 3 3).

  Definition ntreeP (A : Set) : functor := \PK{unit} \PS \PK{ A } \PP \PI \PP \PI.
  Definition ltreeP (A : Set) : functor := \PK{A} \PS \PI \PP \PI.
  Definition CoTree A := Nu (ntreeP A).
  Definition Tree A := Mu (ntreeP A).

  CoFixpoint build1 (n : nat) : CoTree nat :=
    cin (ntreeP nat) (inr (n, build1 (n+1), build1 (n * 2))).

  Eval compute in tryTake 8 (ntreeP nat) (build1 0).

  Close Scope functor_scope.
End ExamplesRec.

(*******************************************************************************)
(** SYNTAX & DEFNS *************************************************************)
(*******************************************************************************)

Parameter aType : Set.
Parameter aTerm : Set.

Inductive type : Set :=
| tyUnit : type
| tyPrim : aType -> type
| tyFun  : type -> type -> type
| tyProd : type -> type -> type
| tySum  : type -> type -> type
| tyApp  : pfun -> type -> type
| tyFix  : pfun -> type
with pfun : Set :=
| fnId   : pfun
| fnCnst : type -> pfun
| fnSum  : pfun -> pfun -> pfun
| fnProd : pfun -> pfun -> pfun.

Scheme type_ind_m := Induction for type Sort Prop
  with pfun_ind_m := Induction for pfun Sort Prop.

Parameter PHasType : aTerm -> type -> Prop.

Fixpoint papp (p : pfun) (t : type) {struct p} : type :=
  match p with
  | fnId         => t
  | fnCnst t'    => t'
  | fnSum  p1 p2 => tySum  (papp p1 t) (papp p2 t)
  | fnProd p1 p2 => tyProd (papp p1 t) (papp p2 t)
  end.

Inductive term : Set :=
| tmPrim  : aTerm -> term

| tmUnit  : term
| tmConst : term -> term
(* Identity and compositon *)
| tmId    : term
| tmComp  : term -> term -> term
(* Products *)
| tmFst   : term
| tmSnd   : term
| tmSplit : term -> term -> term
(* Sum *)
| tmInl   : term
| tmInr   : term
| tmCase  : term -> term -> term
(* Functors *)
| tmMap   : pfun -> term -> term
(* Recursion *)
| tmIn    : pfun -> term
| tmOut   : pfun -> term
(* Hylo *)
| tmRec   : pfun -> term -> term -> term.

Inductive HasType : term -> type -> Prop :=
| TyPrim  : forall p t, PHasType p t -> HasType (tmPrim p) t

| TyUnit  : HasType tmUnit tyUnit
| TyConst : forall e t t', HasType e t -> HasType (tmConst e) (tyFun t' t)

| TyId    : forall t, HasType tmId (tyFun t t)
| TyComp  : forall e1 e2 a b c,
    HasType e1 (tyFun b c) ->
    HasType e2 (tyFun a b) ->
    HasType (tmComp e1 e2) (tyFun a c)

| TyFst   : forall a b, HasType tmFst (tyFun (tyProd a b) a)
| TySnd   : forall a b, HasType tmSnd (tyFun (tyProd a b) b)
| TySplit : forall e1 e2 a b c,
    HasType e1 (tyFun a b) ->
    HasType e2 (tyFun a c) ->
    HasType (tmSplit e1 e2) (tyFun a (tyProd b c))

| TyInl   : forall a b, HasType tmInl (tyFun a (tySum a b))
| TyInr   : forall a b, HasType tmInr (tyFun b (tySum a b))
| TyCase  : forall e1 e2 a b c,
    HasType e1 (tyFun a c) ->
    HasType e2 (tyFun b c) ->
    HasType (tmCase e1 e2) (tyFun (tySum a b) c)

| TyMap   : forall p e a b,
    HasType e (tyFun a b) ->
    HasType (tmMap p e) (tyFun (tyApp p a) (tyApp p b))

| TyIn    : forall p, HasType (tmIn p) (tyFun (tyApp p (tyFix p)) (tyFix p))
| TyOut   : forall p, HasType (tmIn p) (tyFun (tyFix p) (tyApp p (tyFix p)))
| TyRec   : forall p e1 e2 a b,
    HasType e1 (tyFun (papp p b) b) ->
    HasType e2 (tyFun a (papp p a)) ->
    HasType (tmRec p e1 e2) (tyFun a b).

Parameter interp_aType : aType -> Set.
Fixpoint interp_type  (t : type) : Set :=
  match t with
  | tyUnit => unit
  | tyPrim k => interp_aType k
  | tyFun a b => interp_type a ~> interp_type b
  | tyProd a b => interp_type a * interp_type b
  | tySum a b => interp_type a + interp_type b
  | tyApp p a => app (interp_pfun p) (interp_type a)
  | tyFix p => Nu (interp_pfun p)
  end
with
interp_pfun (p : pfun) : functor :=
  match p with
  | fnId => pid
  | fnCnst a => pconst (interp_type a)
  | fnProd p q => pprod (interp_pfun p) (interp_pfun q)
  | fnSum p q => psum (interp_pfun p) (interp_pfun q)
  end.

Parameter interp_aTerm : forall (e : aTerm) (A : Set), A -> Prop.

CoInductive interp_term : forall {A : Set}, term -> A -> Prop :=
| IPrim : forall A p x, interp_aTerm p A x -> interp_term (tmPrim p) x
| IUnit : interp_term tmUnit tt
| IConst : forall (A B : Set) t (x : B),
    interp_term t x ->
    interp_term (tmConst t) (fun (_ : A) => x)

| IId : forall (A : Set), interp_term tmId (fun (x : A) => x)
| IComp : forall {A B C : Set} (e1 : term) (f1 : B -> C) (e2 : term) (f2 : A -> B),
    interp_term e1 f1 ->
    interp_term e2 f2 ->
    interp_term (tmComp e1 e2) (fun x => f1 (f2 x))

| IFst : forall (A B : Set), interp_term tmFst (fun (x : A * B) => fst x)
| ISnd : forall (A B : Set), interp_term tmSnd (fun (x : A * B) => snd x)
| ISplit : forall (A B C : Set) e1 e2 (f1 : A -> B) (f2 : A -> C),
    interp_term e1 f1 ->
    interp_term e2 f2 ->
    interp_term (tmSplit e1 e2) (fun x => (f1 x, f2 x))

| IInl : forall (A B : Set), interp_term tmInl (fun (x : A) => inl B x)
| IInr : forall (A B : Set), interp_term tmInr (fun (x : B) => inr A x)
| ICase : forall (A B C : Set) e1 e2 (f1 : A -> C) (f2 : B -> C),
    interp_term e1 f1 ->
    interp_term e2 f2 ->
    interp_term (tmCase  e1 e2) (fun x => match x with
                                       | inl y => f1 y
                                       | inr y => f2 y
                                 end)

| IMap : forall (A B : Set) (e : term) (f : A -> B) P,
    interp_term e f ->
    interp_term (tmMap P e) (map (interp_pfun P) f)

| IIn  : forall P, interp_term (tmIn  P) (fun x => cin (interp_pfun P) x)
| IOut: forall P, interp_term (tmOut P) (fun x => cout (interp_pfun P) x)
| IRec: forall (A B : Set) P
          e1 (f1 : A -> app (interp_pfun P) A)
          e2 (f2 : app (interp_pfun P) B -> B)
          (f3 : A -> B),
    interp_term e1 f1 ->
    interp_term e2 f2 ->
    interp_term (tmRec P e1 e2) f3 ->
    interp_term (tmRec P e1 e2)
                (fun x => f2 (map (interp_pfun P) f3 (f1 x))).