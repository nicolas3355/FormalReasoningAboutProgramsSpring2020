(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 6 *)

(* In this pset, you will use abstract-interpretation results to enable
 * optimizations in programs:
 * (1) Develop and verify an analysis that just tracks known constant values
 *     for variables.
 * (2) Write and verify an optimization that replaces variables with their known
 *     constant values, which is trickier than it sounds, because variables may
 *     equal different constants at different points in the code!
 * (3) Use all of the above to prove that a particular run of the optimization
 *     generates an optimized program with the same behavior as the original
 *     program. *)

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang
* (wangpeng@csail.mit.edu), Andres Erbsen (andreser@mit.edu) *)

Require Import Frap AbstractInterpret Pset6Sig.
(* Note that module [AbstractInterpret] here duplicates the framework
 * definitions from AbstractInterpretation.v, the file with example code from
 * the last lecture. *)

(** * An abstract interpretation tracking equality to constants *)

(* copy-pasted from Sig file:
Inductive domain :=
| Exactly (n : nat)
| Anything.
*)

Definition represents (x:nat) (d:domain) : Prop :=
  match d with
  | Exactly n => x = n
  | Anything => True
  end.

Definition absint_binop (f : nat -> nat -> nat) (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => Exactly (f n m)
  | _, _ => Anything
  end.

Definition join (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => if n ==n m then Exactly n else Anything
  | _, _ => Anything
  end.

Definition constant_absint := {|
  Top := Anything;
  Constant := Exactly;
  Add := absint_binop Nat.add;
  Subtract := absint_binop Nat.sub;
  Multiply := absint_binop Nat.mul;
  Join := join;
  Represents := represents
|}.

(* copy-pasted from frap/AbstractInterpret.v:
Definition astate (a : absint) := fmap var a.
Definition compatible a (s : astate a) (v : valuation) : Prop := 
  forall x xa, s $? x = Some xa
               -> exists n, v $? x = Some n
                            /\ a.(Represents) n xa. *)

(* Depending on how you approach [constant_sound], this
 * lemma may or may not be useful. Regardless, it is used in our proof of
 * [optimize_program_ok] below. *)
(* from frap/AbstractInterpret.v:
Definition subsumed a (s1 s2 : astate a) :=
  forall x, match s1 $? x with
            | None => s2 $? x = None
            | Some xa1 =>
              forall xa2, s2 $? x = Some xa2
                          -> forall n, a.(Represents) n xa1
                                       -> a.(Represents) n xa2
            end.
*)

Lemma compatible_subsumed : forall a (s1 s2 : astate a) v,
  compatible s1 v -> subsumed s1 s2  -> compatible s2 v.
Proof.
  unfold compatible, subsumed; simplify.
  specialize H0 with (x:=x). cases (s1 $? x).
  apply H in Heq; first_order. equality.
Qed. 
Hint Resolve compatible_subsumed : core.

Lemma constant_sound : absint_sound constant_absint.
Proof.
  split.
  (* You'll need to prove this one. *)

  all: simplify.

  (* As a convenience, here are some examples of how to
   * combine tactics using repeat-match-progress. These are not particularly
   * useful for this goal, just a reference for proof-scripting syntax. *)
  all: try equality.
  all:
    repeat match goal with
    | na : domain |- _
        => progress (cases na; try equality)
    | |- True
       => equality 
    | x : bool |- _
        => progress (cases x)
    | H : Some _ = Some _ |- _
        => progress (invert H)
    | |- Some _ = Some _ =>
        progress (apply f_equal)
    | H : ?x = ?x + 1 |- _
        => solve [linear_arithmetic]
    | H : forall b, b = true -> _ |- _
        => specialize (H true)
    | H : forall n : nat, n = ?x1 -> n = ?x2 |- _
        => specialize (H x1); propositional
    | H : forall n : nat, True -> n = ?x |- _
        => specialize (H (S x))    
    | [ |- context [ ?n1 ==n ?n0 ] ]  
        => cases (n1 ==n n0); simplify; try equality
    | _ => progress (simplify)
    end.
 all: try linear_arithmetic.
Qed.


(** * Optimizing programs based on that analysis *)

(* Our expression evaluator returns one of two outputs, for a particular input
 * expression: *)
(* copy-pasted from sig file:
Inductive constfold_result :=
| Known (n : nat)        (* The variable is exactly [n]. *)
| Simplified (e : arith) (* I don't know the exact value, but it's the same as this
                          * (potentially simplified) expression [e]. *).
*)

(* It's easy to convert a result back into a normal expression. *)
Definition to_arith (r : constfold_result) : arith :=
  match r with
  | Known n => Const n
  | Simplified e => e
  end.

(* The optimizer for expressions is straightforward though a bit fiddly. *)
Fixpoint constfold_arith (e : arith) (s : astate constant_absint) : constfold_result :=
  match e with
  | Const n => Known n
  | Var x =>
    match s $? x with
    | Some (Exactly n) => Known n
    | _ => Simplified e
    end
  | Plus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 + n2)
    | e1', e2' => Simplified (Plus (to_arith e1') (to_arith e2'))
    end
  | Times e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 * n2)
    | e1', e2' => Simplified (Times (to_arith e1') (to_arith e2'))
    end
  | Minus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 - n2)
    | e1', e2' => Simplified (Minus (to_arith e1') (to_arith e2'))
    end
  end.

(* Now we get to the optimizer for commands, which is about as much code, but
 * which is significantly more intricate.  As with [absint_step], we pass a
 * parameter [C], standing for *the context in which this command will be
 * run.*  We also pass [ss], a map from commands to what we know about
 * variables, right before running the corresponding command.  That information
 * is enough for us to replace variable occurrences with their known constant
 * values. *)
Fixpoint constfold_cmd (c : cmd) (ss : astates constant_absint) (C : cmd -> cmd) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
    (* Note how here we query the abstract state [ss] with the current command
     * [c] wrapped in [C].  In other words, we are querying the analysis
     * result, asking "when we reach this command, what is known to be true
     * about the variable values?". *)
    match ss $? C c with
    | None => Assign x e
    | Some s => Assign x (to_arith (constfold_arith e s))
                (* What do we do with what we learn?  If there are variable
                 * values associated with this location in the program, we use
                 * them to optimize the expression being assigned. *)
    end
  | Sequence c1 c2 => Sequence (constfold_cmd c1 ss (fun c' => C (Sequence c' c2)))
                               (constfold_cmd c2 ss C)
  | If e then_ else_ =>
    If e (constfold_cmd then_ ss C)
         (constfold_cmd else_ ss C)
  | While e body =>
    While e (constfold_cmd body ss (fun c' => C (Sequence c' c)))
  end.

Definition compatible_throughout_steps {A} ss v c:= forall c' s v',
  ss $? c' = Some s -> step^* (v, c) (v', c') -> @compatible A s v'.
(* This line makes [eauto] treat [compatible_throughout_steps] as inlined: *)
Hint Unfold compatible_throughout_steps : core.

Lemma one_to_many: forall v c v' c',
  step (v, c) (v', c') ->
  step^* (v, c) (v', c').
Proof.
  induct 1; eauto.
Qed.

Lemma transitivity_step: forall v c v0 c0 v' c',
 step (v, c) (v0, c0) -> (step) ^* (v0, c0) (v', c') -> step^* (v, c) (v', c'). 
Proof.
  induct 1; eauto.
Qed.

Lemma transitivity_steps: forall v c v0 c0 v' c',
 step^* (v, c) (v0, c0) -> (step) ^* (v0, c0) (v', c') -> step^* (v, c) (v', c'). 
Proof.
  induct 1; simplify; eauto.
  cases y.
  specialize (IHtrc v1 c1 v0 c0).
  propositional.
  eapply transitivity_step in H; eauto.
Qed.


Definition interp_once (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.
Lemma interp_once_is_interp : forall e v, interp e v = interp_once e v.
Proof. induct e; simplify; eauto. Qed.

Ltac interp_once := rewrite interp_once_is_interp; unfold interp_once.

Lemma test: forall e a v, compatible a v -> interp e v = interp (to_arith (constfold_arith e a)) v.
Proof.

  induct e.
  try (simplify; eauto; fail).
  intros.
  unfold compatible in H.
  unfold constfold_arith.
  cases (a $? x).
  apply H in Heq.
  invert Heq.
  propositional.
  cases d; eauto.
  simplify.
  rewrite H1; assumption.
  simplify.
  equality.

  all:intros; interp_once; erewrite IHe1; eauto; erewrite IHe2; eauto; symmetry; interp_once; simplify; cases(constfold_arith e1 a); cases (constfold_arith e2 a); simplify; equality.
Qed.

Lemma constfold_step : forall v c v' c',
  step (v, c) (v', c')
  -> forall C ss, (forall a, ss $? C c = Some a -> compatible a v)
  -> step (v, constfold_cmd c ss C) (v', constfold_cmd c' ss C).
Proof.
  induct 1; simplify; eauto.
  cases (ss $? C (x <- e)); eauto.
  invert Heq.
  specialize(H a).
  propositional.
  apply test with (e:=e) in H0.
  rewrite H0.
  constructor.
Qed.

Lemma constfold_one_step_all : forall v c v' c',
  step (v, c) (v', c') ->
  forall ss,  compatible_throughout_steps ss v c ->
  step (v, constfold_cmd c ss (fun c1 => c1))
  (v', constfold_cmd c' ss (fun c1 => c1)).
Proof.
  induct 1; try (simplify; eauto; fail).
  +
    simplify.
    cases (ss $? (x <- e)); simplify; eauto.
    unfold compatible_throughout_steps in H.
    eapply H in Heq.
    eapply test in Heq.
    rewrite Heq.
    constructor 1.
    eauto.
  +
    simplify.
    econstructor.
    eapply constfold_step in H.
    eauto.
    simplify.
    unfold compatible_throughout_steps in H0.
    apply StepSeq1  with (c2:=c2) in H.
    eapply H0 in H1; eauto.
Qed.

Proof.
(* Prove: any sequence of small steps can be replicated with the optimized command. *)
Lemma constfold_steps : forall v c v' c',
  step^* (v, c) (v', c') ->
  forall ss, compatible_throughout_steps ss v c ->
  step^* (v, constfold_cmd c ss (fun c1 => c1))
  (v', constfold_cmd c' ss (fun c1 => c1)).
Proof.
  induct 1.
  simplify.
  constructor.
  
  cases y.
  simplify.
  assert(H':= H).
  eapply constfold_one_step_all in H. 
  2: eauto.
  specialize (IHtrc v0 c0 v' c').
  propositional.
  specialize (H3 ss).
  assert (compatible_throughout_steps ss v0 c0) by eauto; propositional.
  apply transitivity_step with (v':=v') (c':= constfold_cmd c' ss (fun c1 : cmd => c1)) in H; assumption.
Qed.

Lemma steps_add : forall v1 v2 c1 c2 c3,
  step ^* (v1,c1) (v2,c2) -> step ^* (v1,c1;;c3) (v2,c2;;c3).
Proof.
  induct 1; simplify; eauto.
Qed.

Lemma steps_remove_skip : forall v1 v2 c1 c2 ,
  step ^* (v1,c1) (v2, Skip ;; c2) -> step ^* (v1,c1) (v2,c2).
Proof.
  
  induct 1; simplify; eauto.
  cases y.
  specialize (IHtrc v v2 c c2).
  propositional.
  eapply transitivity_step in H; eauto.
Qed.


 Lemma steps_are_eval: forall v c1 v', step^* (v, c1) (v', Skip) -> eval v c1 v'.
 Proof.
   induct 1; eauto.
 Qed.

Lemma eval_are_steps: forall v c1 v', eval v c1 v' -> step^* (v, c1) (v', Skip).
 Proof.
   induct 1; eauto.
   apply transitivity_steps with (v0 := v1) (c0 := Skip ;; c2).
   apply steps_add.
   assumption.

   econstructor.
   instantiate (1 := (v1,c2)).
   econstructor.
   assumption.

   econstructor.
   eauto.

   apply steps_add  with (c3:=while e loop body done) in IHeval1.
   apply steps_remove_skip in IHeval1.
   eapply transitivity_steps; eauto.
 Qed.

Lemma eval_constfold_tmp : forall v c v',
  step^* (v, c) (v', Skip) -> eval v c v' ->
  forall ss, compatible_throughout_steps ss v c -> step^* (v, constfold_cmd c ss (fun c1 => c1))
  (v', constfold_cmd Skip ss (fun c1 => c1)) ->
  eval v (constfold_cmd c ss (fun c1 => c1)) v'.
Proof.
  simplify.
  apply steps_are_eval; eauto.
Qed.

(* Prove: any full program execution can be replicated with the optimized program. *)
Lemma eval_constfold : forall v c v',
  eval v c v' ->
  forall ss, compatible_throughout_steps ss v c ->
  eval v (constfold_cmd c ss (fun c1 => c1)) v'.
Proof.
  simplify.
  eapply eval_constfold_tmp; try assumption.
  apply eval_are_steps; assumption.
  apply eval_are_steps in H.
  apply constfold_steps; assumption.
Qed.

(* This lemma connects the previous to the [invariantFor] goal that FRAP abstract-interpretation machinery proves. *)

Lemma optimize_program_ok : forall v c v' ss,
  eval v c v'
  -> invariantFor (absint_trsys constant_absint c)
                  (fun p => exists s, ss $? snd p = Some s
                                      /\ subsumed (fst p) s)
  -> eval v (constfold_cmd c ss (fun c1 => c1)) v'.
Proof.
  simplify.
  apply eval_constfold; auto.
  eapply invariant_simulates with (sys1 := trsys_of v c) in H0;
    try (apply absint_simulates with (a := constant_absint); apply constant_sound).
  unfold compatible_throughout_steps.
  simplify.
  eapply use_invariant in H0; simplify; eauto.
  invert H0.
  invert H3.
  invert H4.
  invert H0.
  simplify.
  replace s with x in * by equality.
  eauto.
Qed.

(* Optional: Actually run your analysis to justify an automatic optimization. 
 * You won't be graded on that part, but it's satisfying to run to wrap up the assignment! *)

Example loopsy :=
  "a" <- 7;;
  "b" <- 0;;
  while "n" loop
    "b" <- "b" + "a";;
    "n" <- "n" - 1
  done.

Example loopsy_optimized :=
  "a" <- 7;;
  "b" <- 0;;
  while "n" loop
    "b" <- "b" + 7;;
    "n" <- "n" - 1
  done.

(* Here are some hints we add, to get the iteration tactics to work properly. *)
Lemma merge_astates_fok_constant : forall x : option (astate constant_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.
Lemma merge_astates_fok2_constant : forall x (y : option (astate constant_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.
Hint Resolve merge_astates_fok_constant merge_astates_fok2_constant : core.

(* This part takes ~3GB of RAM and 10 minutes on the laptop we tested with. *)
(*
Lemma loopsy_optimized_properly : forall v v',
  eval v loopsy v'
  -> eval v loopsy_optimized v'.
Proof.
  simplify.
  assert (exists ss, invariantFor (absint_trsys constant_absint loopsy)
                                  (fun p => exists s, ss $? snd p = Some s
                                                      /\ subsumed (fst p) s)
                     /\ loopsy_optimized = constfold_cmd loopsy ss (fun c1 => c1)).

  eexists; propositional.
  
  apply interpret_sound.
  apply constant_sound.

  unfold loopsy.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  simplify.
  equality.

  first_order.
  rewrite H1.
  apply optimize_program_ok.
  assumption.
  assumption.
Qed.
*)
