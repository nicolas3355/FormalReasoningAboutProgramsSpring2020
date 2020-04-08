(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 7 *)

(* Authors:
 * Peng Wang (wangpeng@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu)
 * Samuel Gruetter (gruetter@mit.edu)
 *)

Require Import Frap.Frap.
Require Import Pset7Sig.

(* Delete this line if you don't like bullet points and errors like
   "Expected a single focused goal but 2 goals are focused." *)
Set Implicit Arguments.


(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type.  Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies.  Instead, here we
 * will prove soundness of *structural* subtyping, whose rules we'll get to
 * shortly.  The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)
| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.


Hint Constructors  value : core.


(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.
Hint Constructors plug : core.
 
(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.

Hint Constructors step0 : core.
Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

Hint Constructors step : core.
Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupleNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Hint Constructors subtype : core.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.
Hint Constructors proj_t : core.

(* Expression typing relation *)
Inductive hasty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    hasty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2 ->
    hasty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2) ->
    hasty G e2 t1 ->
    hasty G (App e1 e2) t2
| HtTupleNil : forall G,
    hasty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    hasty G e1 t1 ->
    hasty G e2 t2 ->
    hasty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    hasty G e t' ->
    proj_t t' n t ->
    hasty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type.  We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    hasty G e t' ->
    t' $<: t ->
    hasty G e t
.

Hint Constructors hasty : core.
(* Prove these two basic algebraic properties of subtyping. *)

Lemma single_is_tuple : forall t1 t2,
  t1 $<: t2 <-> TupleTypeCons t1 TupleTypeNil $<: TupleTypeCons t2 TupleTypeNil.
Proof.
  simplify.
  propositional; eauto.
  invert H.
  assumption.
Qed.

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  induct t1; eauto.
Qed.

Hint Resolve subtype_refl: core.

(* BEGIN handy tactic that we suggest for these proofs *)
Ltac tac0 :=
  match goal with
  | [ H : ex _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
  | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
  | [ H : step _ _ |- _ ] => invert H
  | [ H : step0 _ _ |- _ ] => invert1 H
  | [ H : hasty _ _ _ |- _ ] => invert1 H
  | [ H : proj_t _ _ _ |- _ ] => invert1 H
  | [ H : plug _ _ _ |- _ ] => invert1 H
  | [ H : subtype _ _ |- _ ] => invert1 H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end;
  subst.
Ltac tac := simplify; subst; propositional; repeat (tac0; simplify; eauto); try equality.
Ltac t := simplify; propositional; repeat (tac0; simplify); try equality; eauto 6.

Lemma subtype_trans_tmp : forall t2 t1 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  induct t2; tac.
  invert H0; eauto.
Qed.

Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  simplify; eapply subtype_trans_tmp; eauto.
Qed.

Hint Resolve subtype_trans: core.
(* END handy tactic *)

Lemma type_abs_value_abs: forall x e a b,
  hasty x e (Fun a b) -> value e -> exists f g, value (Abs f g).
Proof.
  cases 2; simplify; eexists; eexists; econstructor.
  Unshelve.
  all: (exact "" || exact (Var "")).
Qed.
Hint Resolve type_abs_value_abs.

Lemma type_fun_abs: forall x t f g,
  hasty x (Abs f g) t -> exists a b, Fun a b $<: t.
Proof.
  induct 1; tac; eauto.
Qed.
Hint Resolve type_fun_abs.


Lemma hasty_TupleCons G e e' t:
  hasty G (TupleCons e e') t ->
  exists t1 t2, hasty G e t1 /\ hasty G e' t2 /\ TupleTypeCons t1 t2 $<: t.
Proof.
  induct 1; eauto.
  invert IHhasty.
  invert H1.
  eexists.
  eexists.
  propositional; eauto.
Qed.

Hint Resolve hasty_TupleCons.

Lemma hasty_TupleNil G t:
  hasty G TupleNil t -> t = TupleTypeNil.
Proof.
  induct 1; tac.
Qed.

Hint Resolve hasty_TupleNil.

Lemma hasty_App G x1 x2 t:
  hasty G (App x1 x2) t ->
  exists t2 t3, hasty G x1 t2 /\ t2 $<: Fun t3 t /\ hasty G x2 t3.
Proof.
  induct 1; tac; eauto.
  eexists; eexists.
  propositional; eauto.
Qed.
Hint Resolve hasty_App : core.

Lemma hasty_Abs G x body t:
  hasty G (Abs x body) t ->
    exists a b , Fun a b $<: t /\ hasty (G $+ (x,a)) body b.
Proof.
  induct 1; tac; eauto.
Qed.

Hint Resolve hasty_Abs : core.

Lemma hasty_proj0 G x tail t:
  hasty G (Proj (TupleCons x tail) 0) t
  -> exists a tail_type, hasty G x a /\ a $<: t /\ hasty G (TupleCons x tail) (TupleTypeCons a tail_type).
Proof.
  induct 1.
  eapply hasty_TupleCons in H.
  tac.
  eexists; eexists.
  propositional; eauto.
  tac.
  eexists.
  eexists.

  propositional; eauto.
Qed.

Hint Resolve hasty_proj0 : core.

Lemma hasty_proj G x tail t n:
  hasty G (Proj (TupleCons x tail) (S n)) t ->
    exists t', hasty G (Proj tail n) t' /\ t' $<: t.
Proof.
  induct 1; tac; eauto.
  eapply hasty_TupleCons in H.
  tac.
Qed.

Hint Resolve hasty_proj : core.

Definition isTupleType t :=
  match t with
  |  TupleTypeCons a b => True
  |  TupleTypeNil => True
  | Fun _ _ => False
  end.
Hint Unfold isTupleType.

Lemma type_fun_is_not_tuple: forall t1 t2,
  isTupleType t1 -> (t1 $<: t2 \/ t2 $<: t1) -> isTupleType t2.
Proof.
  unfold isTupleType.
  simplify.
  cases t1; cases t2; tac.
Qed.

Hint Resolve type_fun_is_not_tuple: core.

Lemma hastype_tuple : forall x t a b,
  (hasty x TupleNil t \/ hasty x (TupleCons a b) t) -> isTupleType t.
Proof.
  simplify.
  propositional; tac.
  induct H0; eauto.
  induct H0; eauto.
Qed.
Hint Resolve hastype_tuple: core.

Lemma hastype_tuple_nil : forall x t,
  hasty x TupleNil t -> isTupleType t.
Proof.
  simplify.
  eapply hastype_tuple.
  left.
  eassumption.
  Unshelve.
  all:exact (Var "").
Qed.
Hint Resolve hastype_tuple_nil : core.

Lemma hastype_tuple_cons : forall x t a b,
  hasty x (TupleCons a b) t -> isTupleType t.
Proof.
  simplify.
  eapply hastype_tuple.
  right.
  eassumption.
Qed.
Hint Resolve hastype_tuple_cons : core.

Lemma tuple_type_cons : forall (t' t t2 :type),
   t' $<: TupleTypeCons t t2 -> exists a b, t' = TupleTypeCons a b.
Proof.
  induct 1; eauto.
Qed.
Hint Resolve tuple_type_cons : core.

Lemma hastype_tuple_cons_generalized : forall x t a b,
  hasty x (TupleCons a b) t -> exists n m, TupleTypeCons n m $<: t.
Proof.
  induct 1; eauto.
  eapply HtSub in H; eauto.
  tac.
Qed.
Hint Resolve hastype_tuple_cons_generalized : core.
(*
Lemma tuple_type : forall t,
   t $<: TupleTypeNil -> t = TupleTypeNil \/ exists a b, t = TupleTypeCons a b.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve tuple_type.
*)
Lemma cheese : forall x e a b,
  hasty x e (Fun a b) -> value e -> exists c d, e = Abs c d.
Proof.
  induct 1; eauto.
  simplify.
  invert H0.
  simplify.
  invert H1.
  invert 1.
  simplify.
  cases t'.
  eapply IHhasty; eauto.
  specialize type_fun_is_not_tuple with (t1 := TupleTypeNil) (t2 := Fun a b).
  simplify; propositional; eauto.
  specialize type_fun_is_not_tuple with (t1 := TupleTypeCons t'1 t'2) (t2 := Fun a b).
  simplify; propositional; eauto.
Qed.
Hint Resolve cheese : core.

Lemma tazz : forall a b t,
   Fun a b $<: t -> exists c d, t = Fun c d.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve tazz : core.

Lemma tazz_rev : forall a b t,
   t $<: Fun a b -> exists c d, t = Fun c d.
Proof.
  induct 1; eauto.
Qed.
Hint Resolve tazz_rev : core.


(*Lemma tuple_type_cons_2 : forall (t' t t2 :type) n,
 t' $<: TupleTypeCons t t2 -> proj_t t2 n t -> t' = TupleTypeCons t2 TupleTypeNil.
Proof.
invert 1; eauto.*)
Hint Resolve tuple_type_cons.
Lemma ho: forall e t t2,
  hasty $0 e (TupleTypeCons t t2) -> value e -> exists e' : exp, step (Proj e 0) e'.
Proof.
induct 1; simplify; eauto.
invert H.
invert H1.
invert H1.
eexists.
eauto.
invert H1.
apply tuple_type_cons in H0.
invert H0.
invert H2.
eauto.
Qed.

(*Lemma test: forall e x x0 n, hasty $0 e (TupleTypeCons x x0) -> proj_t x0 n x.
Proof.
  induct 1; eauto.
*)

Lemma tuple_cons : forall e t t2,
  hasty $0 e (TupleTypeCons t t2) -> value e -> exists a b, e = TupleCons a b.
Proof.
  induct 1; simplify; tac; eauto.
  invert H1.
  invert H1.
Qed.
Hint Resolve tuple_cons : core.

Lemma ho': forall e t t2 n,
  hasty $0 e (TupleTypeCons t t2) -> value e -> exists e' : exp, step (Proj e (S n)) e'.
Proof.
  simplify.
  specialize (tuple_cons H H0).
  simplify.
  tac.
  invert H0.
  eauto.
Qed.

  (* Now we're ready for the first of the two key properties to establish that
   * invariant: well-typed programs are never stuck. *)
Lemma progress : forall e t,
  hasty $0 e t
  -> value e
  \/ (exists e' : exp, step e e').
Proof.
  induct 1; eauto.
  + right.
    propositional; tac.
    assert (Hx := H3).
    eapply cheese in H3; eauto.
    tac.
  + propositional; tac; eauto 10.
  + propositional; tac; eauto 10.
    right; tac.

    induct H0; tac.
    ++ eapply ho; eauto.
    ++ eapply ho'; eauto.
Qed.

Hint Resolve progress: core.

(* Inclusion between typing contexts is preserved by adding the same new mapping
 * to both. *)
Lemma weakening_override : forall (G G' : fmap var type) x t,
  (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
  -> (forall x' t', G $+ (x, t) $? x' = Some t'
                    -> G' $+ (x, t) $? x' = Some t').
Proof.
  tac.
Qed.

Hint Resolve weakening_override.

(* This lemma lets us transplant a typing derivation into a new context that
 * includes the old one. *)
Lemma weakening : forall G e t,
  hasty G e t
  -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
    -> hasty G' e t.
Proof.
  induct 1; simplify; eauto; tac; try econstructor; tac.
Qed.

Hint Resolve weakening.


Lemma hasty_change : forall G e t,
  hasty G e t
  -> forall G', G' = G
    -> hasty G' e t.
Proof.
  tac.
Qed.

Hint Resolve hasty_change : core.


(* Replacing a variable with a properly typed term preserves typing. *)
Lemma substitution : forall G x t' e t e',
  hasty (G $+ (x, t')) e t
  -> hasty $0 e' t'
  -> hasty G (subst e' x e) t.
Proof.
  induct 1; tac; eauto.
Qed.

Hint Resolve substitution: core.

(*
Lemma projn_type : forall v1 v2 tuple_type G n t2,
  hasty G (Proj (TupleCons v1 v2) n) t2 -> proj_t t n t2 -> hasty G v1 t2.
Proof.
  simplify.


  Print proj_t.
  induct 2.

Admitted.
*)

(* We're almost ready for the other main property.  Let's prove it first
 * for the more basic [step0] relation: steps preserve typing. *)
Lemma preservation0 : forall e1 e2,
  step0 e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  induct 1; tac; eauto.
  eapply hasty_App in H0; tac.
  eapply hasty_Abs in H1; tac.
  eapply substitution; eauto.
  eapply hasty_proj0 in H1; tac.
  eapply hasty_proj in H1; tac.
Qed.

Hint Resolve preservation0.
(* We also need this key property, essentially saying that, if [e1] and [e2] are
 * "type-equivalent," then they remain "type-equivalent" after wrapping the same
 * context around both. *)
Lemma generalize_plug : forall e1 C e1',
  plug C e1 e1'
  -> forall e2 e2', plug C e2 e2'
    -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
    -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.
  induct 1; tac; eauto.
  eapply hasty_App in H2; tac.
  eapply hasty_App in H3; tac.
  eapply hasty_TupleCons in H2; tac.
  eapply hasty_TupleCons in H3; tac.
  induct H2; eauto.
Qed.

  Hint Resolve generalize_plug.

(* OK, now we're almost done.  Full steps really do preserve typing! *)
Lemma preservation : forall e1 e2,
  step e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; tac.
  eauto.
Qed.

Hint Resolve preservation.
(* The real prize: prove soundness of this type system.
 * We suggest starting from a copy of the type-safety proof from the book's
 * LambdaCalculusAndTypeSoundness.v.
 * The soundness argument for simply typed lambda calculus is genuinely difficult
 * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
 * task of this pset is to *extend* it to cover subtyping. This will involve
 * changing some proofs, and making appropriate additional helper lemmas (there
 * are more hints on the website).
 * Trying to write this proof from scratch is *not* recommended for this pset.
 * This is in contrast to the *previous* psets, which we tried to design so that
 * they could be solved from scratch a with good understanding of the lecture
 * material. *)
Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t); eauto.
    apply invariant_induction; tac; eauto; try equality.
Qed.

