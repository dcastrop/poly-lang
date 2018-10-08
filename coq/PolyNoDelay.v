(** Delay monad ****************************************************************)

CoInductive CoNat : Set :=
| CO : CoNat
| CS : CoNat -> CoNat.

Definition peekN (x : CoNat) : CoNat :=
  match x with
  | CO => CO
  | CS m => CS m
  end.

Theorem peekNThm : forall (x : CoNat), x = peekN x.
Proof.
  destruct x; reflexivity.
Qed.

CoInductive Delay (t : Type) : Type :=
| Now  : t -> Delay t
| Wait : Delay t -> Delay t.
Arguments Now {t} v.
Arguments Wait {t} d.

CoFixpoint steps {A} (x : Delay A) : CoNat :=
  match x with
  | Now _ => CO
  | Wait w => CS (steps w)
  end.

CoFixpoint roll {A} (x : A) (n : CoNat) : Delay A :=
  match n with
  | CO => Now x
  | CS m => Wait (roll x m)
  end.

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

(*
Theorem simApprox : forall A (d1 d2 : Delay A), sim A d1 d2 -> approxEq A d1 d2.
Proof.
  intros A d1 d2 H v.
  split; revert d1 d2 H v; cofix; intros d1 d2 H v E.
  - inversion H; subst; inversion E; subst; constructor.
    apply (simApprox w1 w2 H0); assumption.
  - inversion H; subst; inversion E; subst; constructor.
    apply (simApprox w1 w2 H0); assumption.
Qed.

CoFixpoint bot {A} : Delay A := Wait bot.

(* The below is definitely not true! What is true is
   forall v, eval bot v*)
Lemma approxBot : forall A (d1 : Delay A), approxEq A d1 bot.
Proof.
  intros A d1 v; split.
  - intros _; cofix CH; rewrite (peekThm _ bot);
      unfold bot; simpl; fold (@bot A);
        constructor; assumption.
  - revert d1; cofix CH;intros [v1 | w1] H.
Abort.
*)

CoFixpoint bind {A B} (x : Delay A) : (forall (v : A), eval A x v -> Delay B) -> Delay B :=
  match x return (forall (v : A), eval A x v -> Delay B) -> Delay B with
  | Now v => fun f => f v (eNow v)
  | Wait w => fun f => Wait (bind w (fun v' p' => f v' (eWait p')))
  end.
Arguments bind {_ _}.

Notation "m >>= f" := (bind m f) (at level 42, left associativity).
Notation "m1 >> m2" := (bind m1 (fun _ => m2)) (at level 42, left associativity).
Definition mret t (x : t) := Now x.
Arguments mret {t} x.

(*
Lemma bindWait : forall A B (x : A) (y : B) (m : Delay A) (f : forall (x : A), eval A m x -> Delay B)
                   (pr0 : eval A m x) (pr1 : eval B (Wait m >>= f) y),
    eval B (m >>= fun v pr => f v (eWait m x pr)).
*)

(*
CoFixpoint appWait (w : Delay A) (x : A) (e : eval A w x) (c : T )
*)

CoFixpoint delay A (n : CoNat) (x : Delay A) : Delay A :=
  match n with
  | CO => x
  | CS m => Wait (delay A m x)
  end.

Definition fwait {A B} (w : Delay A)
           (f : forall (y : A), eval A (Wait w) y -> Delay B)
           (y : A) (w : eval A w y) : Delay B :=
  f y (eWait w).

Lemma evalBind : forall A B (x : A) (y : B) (m : Delay A) (f : forall (x : A), eval A m x -> Delay B)
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

Fixpoint poly (f : functor) : Prop :=
  match f with
  | pid => True
  | pconst _ => True
  | pprod p1 p2 => poly p1 /\ poly p2
  | psum  p1 p2 => poly p1 /\ poly p2
  | pexp  _  _  => False
  end.

Notation " \PI " := (pid) (at level 0) : functor_scope.
Notation " \PK{ X }" := (pconst X) (at level 0) : functor_scope.
Notation " l \PP r " := (pprod l r) (at level 40, left associativity) : functor_scope.
Notation " l \PS r " := (psum l r) (at level 50, left associativity) : functor_scope.

Fixpoint app (p : functor) (x : Set) : Set :=
  match p with
  | pid => x
  | pconst y => y
  | pprod p1 p2 => app p1 x * app p2 x
  | psum p1 p2 => app p1 x + app p2 x
  | pexp d c => d -> app c x
  end %type.


Fixpoint fmap {A B : Set} (F : functor) (f : A -> B) (x : app F A) : app F B :=
  match F return app F A -> app F B with
  | pid => fun x => f x
  | pconst _ => fun y => y
  | pprod G H => fun x => (fmap G f (fst x), fmap H f (snd x))
  | psum G H => fun x => match x with
                     | inl y => inl (fmap G f y)
                     | inr y => inr (fmap H f y)
                     end
  | pexp _ C => fun x y => fmap C f (x y)
  end x.

Definition shape (P : functor) : Set := app P unit.

Fixpoint position (p : functor) : shape p -> Set :=
  match p return shape p -> Set with
  | pid          => fun _ => unit
  | pconst x     => fun _ => Empty_set
  | pprod  p1 p2 => fun s => position p1 (fst s) + position p2 (snd s)
  | psum   p1 p2 => fun s => match s with
                         | inl s' => position p1 s'
                         | inr s' => position p2 s'
                         end
  | pexp  D p1   => fun s => {x : D & position p1 (s x) }
  end %type.

Inductive App (P : functor) (X : Set) : Set :=
| AppI : forall (s : shape P) (c : position P s -> X), App P X.
Arguments AppI {_ _}.

Fixpoint fromApp_ {X : Set} P : forall (s : shape P),  (position P s -> X) -> app P X :=
  match P return forall (s : shape P), (position P s -> X) -> app P X with
  | pid         => fun _ f => f tt
  | pconst _    => fun x _ => x
  | pprod p1 p2 => fun x f => (fromApp_ p1 (fst x) (fun i => f (inl i)),
                           fromApp_ p2 (snd x) (fun i => f (inr i)))
  | psum  p1 p2 =>
    fun x => match x return (position (psum p1 p2) x -> X) -> app (psum p1 p2) X
          with
          | inl l => fun f => inl (fromApp_ p1 l f)
          | inr r => fun f => inr (fromApp_ p2 r f)
          end
  | pexp  D p1 =>
    fun x f d => fromApp_ p1 (x d) (fun i => f (existT _ d i))
  end.

Definition fromApp {X : Set} P (a : App P X) : app P X :=
  match a with
  | AppI s c => fromApp_ P s c
  end.

Definition shapeOf {X : Set} P (x : App P X) : shape P
  := match x with AppI s _ => s end.

Definition positionOf {X : Set} P (x : App P X) : position P (shapeOf P x) -> X
  := match x with AppI _ f => f end.

Fixpoint toApp {X : Set} P : app P X -> App P X :=
  match P return app P X -> App P X with
  | pid          => fun x => @AppI pid        X tt (fun _ => x)
  | pconst A     => fun x => @AppI (pconst A) X x  (fun e => match e with end)
  | pprod  P1 P2 =>
    fun x => match x with
          | (l, r) => match toApp P1 l, toApp P2 r with
                     | AppI xl fl, AppI xr fr =>
                       @AppI (pprod P1 P2) X
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
                    | AppI xy fy => @AppI (psum P1 P2) X (inl xy) fy
                    end
          | inr y => match toApp P2 y with
                    | AppI xy fy => @AppI (psum P1 P2) X (inr xy) fy
                    end
          end
  | pexp   D  P1 =>
    fun x => @AppI (pexp D P1) X
                (fun d => shapeOf P1 (toApp P1 (x d)))
                (fun p => positionOf P1 (toApp P1 (x (projT1 p))) (projT2 p))
  end.

(* (* THIS FAILS LATER WHEN BUILDING INFINITE DATA! *)
Definition shapeOf {X : Set} P : app P X -> shape P :=
  fmap P (fun _ => tt).

Fixpoint positionOf {X : Set} P
  : forall (x : app P X), position P (shapeOf P x) -> X
  := match P return forall (x : app P X), position P (shapeOf P x) -> X with
     | pid          => fun x _ => x
     | pconst X     => fun x e => match e with end
     | pprod  P1 P2 => fun x   => match x with
                              | (l, r) => fun c => match c with
                                               | inl c' => positionOf P1 l c'
                                               | inr c' => positionOf P2 r c'
                                               end
                              end
     | psum   P1 P2 => fun x   => match x with
                              | inl y => fun c => positionOf P1 y c
                              | inr y => fun c => positionOf P2 y c
                              end
     | pexp   D  P1 => fun x c => match c with
                              | existT _ d c' => positionOf P1 (x d) c'
                              end
     end.

Definition toApp {X : Set} P (x : app P X) : App P X :=
  @AppI P X (shapeOf P x) (positionOf P x).
*)


Inductive Mu (P : functor) : Set :=
| MuI : App P (Mu P) -> Mu P.
Arguments MuI {_}.

CoInductive Nu (P : functor) : Set :=
| NuI : App P (Nu P) -> Nu P.
Arguments NuI {_}.

Definition iin  {P} (x : app P (Mu P)) : Mu P := MuI (toApp P x).
Definition iout {P} (x : Mu P) : app P (Mu P) :=
  match x with
  | MuI z => fromApp P z
  end.

Definition cin  P (x : app P (Nu P)) : Nu P := NuI (toApp P x).
Definition cout P (x : Nu P) : app P (Nu P) :=
  match x with
  | NuI z => fromApp P z
  end.

Fixpoint approx (n : nat) P X : Set :=
  match n with
  | O => X
  | S m => app P (approx m P X)
  end.

Notation " P ^ n " := (approx n P) (at level 30, right associativity).

Fixpoint unroll (n : nat) P (x : Nu P) : (P^n) (Nu P) :=
  match n return (P^n) (Nu P) with
  | O => x
  | S m => fmap P (unroll m P) (cout P x)
  end.

Fixpoint take (n : nat) P (x : Nu P) : (P^n) unit :=
  match n return (P^n) unit with
  | O => tt
  | S m => fmap P (take m P) (cout P x)
  end.

Section ExamplesRec.
  Open Scope functor_scope.

  Definition natP : functor := \PK{unit} \PS \PI.

  Definition listP (A : Set) : functor := \PK{unit} \PS \PK{ A } \PP \PI.
  Definition CoList A := Nu (listP A).
  Definition List A := Mu (listP A).

  CoFixpoint build0 (n : nat) : CoList nat :=
    cin (listP nat) (inr (n, build0 (S n))).

  Eval compute in take 20 (listP nat) (build0 0).

  Definition ntreeP (A : Set) : functor := \PK{unit} \PS \PK{ A } \PP \PI \PP \PI.
  Definition ltreeP (A : Set) : functor := \PK{A} \PS \PI \PP \PI.
  Definition CoTree A := Nu (ntreeP A).
  Definition Tree A := Mu (ntreeP A).

  CoFixpoint build1 (n : nat) : CoTree nat :=
    cin (ntreeP nat) (inr (n, build1 (n+1), build1 (n * 2 + 1))).

  Eval compute in take 6 (ntreeP nat) (build1 0).

  Close Scope functor_scope.
End ExamplesRec.

Definition pmap {X Y : Set} P (f : X -> Y) (v : App P X) : App P Y :=
  match v with
  | AppI s g => AppI s (fun s => f (g s))
  end.

CoInductive stream A :=
| Cons : A -> stream A -> stream A.

(*
Definition bad_tl {A} (x : stream A) : stream A :=
  match x with
  | Cons _ x s => s
  end.

Fail CoFixpoint bad {A} (x : A) : stream A :=
  bad_tl (Cons A x (bad x)).

(* Must make sure if corecursive call occurs as argument of function, it ends up
being productive anyway *)
Definition good_tl {A} (x : stream A) : stream A :=
  match x with
  | Cons _ x (Cons _ y s) => Cons _ x s
  end.

CoFixpoint good {A} (x : A) : stream A :=
  good_tl (Cons A x (Cons A x (good x))).

*)

Fixpoint waitP0 {X : Set} (P : functor)
  : poly P -> app P (Delay X) -> Delay (app P X) :=
  match P return poly P -> app P (Delay X) -> Delay (app P X) with
  | pid         => fun _  x => x
  | pconst _    => fun _  x => Now x
  | pprod P1 P2 => fun pl x => waitP0 P1 (proj1 pl) (fst x) >>=
                                  fun l _ => waitP0 P2 (proj2 pl) (snd x) >>=
                                                 fun r _ => mret (l, r)
  | psum P1 P2 => fun pl x =>
                   match x with
                   | inl y => waitP0 P1 (proj1 pl) y >>= fun z _ => mret (inl z)
                   | inr y => waitP0 P2 (proj2 pl) y >>= fun z _ => mret (inr z)
                   end
  | pexp _ _ => fun pl _ => False_rec _ pl
  end.

(** Recursive types + delay ****************************************************)

Fixpoint papp (P : functor) (A : Set) : Set :=
  match P with
  | pid => A
  | pconst X => X
  | pprod P1 P2 => papp P1 A * papp P2 A
  | psum P1 P2 => papp P1 A + papp P2 A
  | pexp D P1 => D ~> papp P1 A
  end.

Fixpoint fmapD {A B : Set} (P : functor) (f : A ~> B) : papp P A ~> papp P B :=
  match P return papp P A ~> papp P B with
  | pid => fun x => f x
  | pconst _ => fun y => mret y
  | pprod P1 P2 => fun x => fmapD P1 f (fst x) >>=
                              fun l _ => fmapD P2 f (snd x) >>=
                                            fun r _ => mret (l, r)
  | psum P1 P2 => fun x => match x with
                       | inl y => fmapD P1 f y >>= fun z _ => mret (inl z)
                       | inr y => fmapD P2 f y >>= fun z _ => mret (inr z)
                   end
  | pexp D P => fun g => mret (fun r => g r >>= fun v _ => fmapD P f v)
  end.

Definition pshape (P : functor) : Set := papp P unit.

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

Fixpoint pos (p : functor) : pshape p -> Set :=
  match p return papp p unit -> Set with
  | pid          => fun _ => unit
  | pconst x     => fun _ => Empty_set
  | pprod  p1 p2 => fun s => pos p1 (fst s) + pos p2 (snd s)
  | psum   p1 p2 => fun s => match s with
                         | inl s' => pos p1 s'
                         | inr s' => pos p2 s'
                         end
  | pexp  D p1   => fun s => posExp D p1 s (pos p1)
  end %type.

CoInductive Pap (P : functor) (X : Set) : Set :=
| PapC : forall (s : pshape P), (pos P s ~> X) -> Pap P X.
Arguments PapC {_ _}.

Definition pshapeOf {X} P (x : Pap P X) : pshape P :=
  match x with
  | PapC s _ => s
  end.

Definition posOf {X} P (x : Pap P X) : pos P (pshapeOf P x) ~> X :=
  match x return pos P (pshapeOf P x) ~> X with
  | PapC _ p => p
  end.

Fixpoint fromPap_ {X : Set} P : forall (s : pshape P), (pos P s ~> X) ~> papp P X :=
  match P return forall (s : pshape P), (pos P s ~> X) ~> papp P X with
  | pid => fun s f => f tt
  | pconst _ => fun s f => mret s
  | pprod P1 P2 =>
    fun s f => fromPap_ P1 (fst s) (fun i => f (inl i)) >>=
                    fun lv _ => fromPap_ P2 (snd s) (fun i => f (inr i)) >>=
                                   fun rv _ => mret (lv, rv)
  | psum P1 P2 =>
    fun s => match s with
          | inl s' => fun f => fromPap_ P1 s' f >>= fun rv _ => mret (inl rv)
          | inr s' => fun f => fromPap_ P2 s' f >>= fun rv _ => mret (inr rv)
          end
  | pexp D P1 =>
    fun s f => mret (fun d => s d >>= fun r p => fromPap_ P1 r (fun i => f (PExp d r p i)))
  end.

Definition fromPap {X : Set} P (v : Pap P X) : Delay (papp P X) :=
  fromPap_ P (pshapeOf P v) (posOf P v).

Definition castShape {P1} {v0 v1 : pshape P1} (eq : v0 = v1)
  : pos P1 v0 -> pos P1 v1 :=
  match eq in (_ = v1) return pos P1 v0 -> pos P1 v1 with
  | eq_refl => fun x => x
  end.


Fixpoint toPap {X : Set} P : papp P X -> Pap P X :=
  match P return papp P X -> Pap P X with
  | pid          => fun x => @PapC pid        X tt (fun _ => mret x)
  | pconst A     => fun x => @PapC (pconst A) X x  (fun e => match e with end)
  | pprod  P1 P2 =>
    fun x => match x with
          | (l, r) => match toPap P1 l, toPap P2 r with
                     | PapC xl fl, PapC xr fr =>
                       @PapC (pprod P1 P2) X
                             (xl, xr)
                             (fun e => match e with
                                    | inl e' => fl e'
                                    | inr e' => fr e'
                                    end)
                     end
          end
  | psum   P1 P2 =>
    fun x => match x with
          | inl y => match toPap P1 y with
                    | PapC xy fy => @PapC (psum P1 P2) X (inl xy) fy
                    end
          | inr y => match toPap P2 y with
                    | PapC xy fy => @PapC (psum P1 P2) X (inr xy) fy
                    end
          end
  | pexp   D  P1 =>
    fun x => @PapC (pexp D P1) X
                (fun d => x d >>= fun v _ => mret (pshapeOf P1 (toPap P1 v)))
                (fun p => x (valueOfPos p)
                         >>= fun v1 pr1 =>
                               posOf P1
                                     (toPap P1 v1)
                                     (castShape
                                        (evalNow (evalBind pr1 (evalOfPos p)))
                                        (nextPos p)))
  end.


Fixpoint appToPapp {X : Set} (P : functor) : app P X -> papp P X :=
  match P return app P X -> papp P X with
  | pid => fun x => x
  | pconst _ => fun x => x
  | pprod p1 p2 => fun x => (appToPapp p1 (fst x), appToPapp p2 (snd x))
  | psum p1 p2 => fun x => match x with
                       | inl y => inl (appToPapp p1 y)
                       | inr y => inr (appToPapp p2 y)
                       end
  | pexp D p => fun f x => Now (appToPapp p (f x))
  end.

CoFixpoint hylo {B : Set} (P : functor)
           (f : papp P B ~> B) (x : Nu P) : Delay B :=
  let h : Nu P ~> B := hylo P f in
   (fix mapr P0 : papp P0 (Nu P) ~> papp P0 B
           := match P0 return papp P0 (Nu P) ~> papp P0 _ with
              | pid => fun x => Wait (h x)
              | pconst _ => fun x => Now x
              | pprod P1 P2 => fun x => mapr P1 (fst x) >>=
                                         fun l => mapr P2 (snd x) >>=
                                                    fun r => mret (l, r)
              | psum P1 P2 => fun x => match x with
                                   | inl y => mapr P1 y >>=
                                                  fun r => mret (inl r)
                                   | inr y => mapr P2 y >>=
                                                  fun r => mret (inr r)
                                   end
              | pexp D P => fun x => mret (fun r => x r >>= fun v => mapr P v)
              end) P (appToPapp P (cout P x))
                     >>= fun r => Wait (f r).

(* Interleave map and corecursion for building Hylo, instead of fmap? *)


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
| tyFix  : pfun -> type
with pfun : Set :=
| fnId   : pfun
| fnCnst : type -> pfun
| fnSum  : pfun -> pfun -> pfun
| fnProd : pfun -> pfun -> pfun.

Scheme type_ind_m := Induction for type Sort Prop
  with pfun_ind_m := Induction for pfun Sort Prop.

Parameter PHasType : aTerm -> type -> Prop.

Fixpoint apply (p : pfun) (t : type) {struct p} : type :=
  match p with
  | fnId         => t
  | fnCnst t'    => t'
  | fnSum  p1 p2 => tySum  (apply p1 t) (apply p2 t)
  | fnProd p1 p2 => tyProd (apply p1 t) (apply p2 t)
  end.

Notation ":[ p ] t" := (apply p t) (at level 0).

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

| TyIn    : forall p, HasType (tmIn p) (tyFun (:[p] (tyFix p)) (tyFix p))
| TyOut   : forall p, HasType (tmIn p) (tyFun (tyFix p) (:[p] (tyFix p)))
| TyRec   : forall p e1 e2 a b,
    HasType e1 (tyFun (:[p] b) b) ->
    HasType e2 (tyFun a (:[p] a)) ->
    HasType (tmRec p e1 e2) (tyFun a b).

(** Interpretation of types **)

Parameter interp_aType : aType -> Set.

Fixpoint interp_type  (t : type) : Set :=
  match t with
  | tyUnit => unit
  | tyPrim k => interp_aType k
  | tyFun a b => interp_type a -> interp_type b
  | tyProd a b => interp_type a * interp_type b
  | tySum a b => interp_type a + interp_type b
  | tyFix p => Rec (interp_pfun p)
  end
with
interp_pfun (p : pfun) : Set -> Set :=
  match p with
  | fnId => fun x => x
  | fnCnst a => fun _ => interp_type a
  | fnProd p q => fun x => (interp_pfun p x * interp_pfun q x)%type
  | fnSum p q => fun x => (interp_pfun p x + interp_pfun q x)%type
  end.

(** Interpretation of terms **)

Parameter interp_aTerm : forall (e : aTerm) (t : type), HasType (tmPrim e) t -> interp_type t.

Fixpoint interp_term (e : term) (t : type) (wt : HasType e t) : interp_type t :=
  match e return forall t, HasType e t -> interp_type t with
  | tmPrim p => fun t wt => interp_aTerm p t wt
  end.