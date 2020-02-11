(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 1 *)

Require Import Frap Pset1Sig.

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and prove some properties of these definitions.
 *)

(* Define [Neg] so that it implements Boolean negation, which flips
 * the truth value of a Boolean value.
 *)
Definition Neg (b : bool) : bool := 
  match b with
    | true => false
    | false => true
  end.

(* For instance, the negation of [true] should be [false].
 * This proof should follow from reducing both sides of the equation
 * and observing that they are identical.
 *)
Theorem Neg_true : Neg true = false.
Proof.
simplify.
equality.
Qed.
(* Negation should be involutive, meaning that if we negate
 * any Boolean value twice, we should get the original value back.

 * To prove a fact like this that holds for all Booleans, it suffices
 * to prove the fact for both [true] and [false] by using the
 * [cases] tactic.
 *)
Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
Proof.
  simplify.
  cases b; try (simplify; equality).
Qed.

(* Define [And] so that it implements Boolean conjunction. That is,
 * the result value should be [true] exactly when both inputs
 * are [true].
 *)
Definition And (x y : bool) : bool := 
  match x,y with
    | true, true => true
    | _, _ => false
  end.

(* Here are a couple of examples of how [And] should act on
 * concrete inputs.
 *)
Theorem And_true_true : And true true = true.
Proof.
simplify.
equality.
Qed.

Theorem And_false_true : And false true = false.
Proof.
simplify.
equality.
Qed.

(* Prove that [And] is commutative, meaning that switching the order
 * of its arguments doesn't affect the result.
 *)
Theorem And_comm : forall x y : bool, And x y = And y x.
Proof.
simplify.
cases x; (cases y; simplify; equality).
Qed.
(* Prove that the conjunction of a Boolean value with [true]
 * doesn't change that value.
 *)
Theorem And_true_r : forall x : bool, And x true = x.
Proof.
simplify.
cases x; simplify; equality.
Qed.

(* In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Print Prog.


(* Define [run] such that [run p n] gives the final state
 * that running the program [p] should result in, when the
 * initial state is [n].
 *)
Fixpoint run (p : Prog) (initState : nat) : nat :=
  match p with
    | Done => initState
    | AddThen e1 p1 => run p1 (initState + e1)
    | MulThen e2 p2 => run p2 (initState * e2)
    | DivThen e3 p3 => run p3 (initState / e3)
    | VidThen e4 p4 => run p4 (e4 / initState)
    | SetToThen e5 p5 => run p5 e5
end.

Print Prog.
Example test := (MulThen 5 (AddThen 2 Done)).
Compute run test 2.
Theorem run_Example1 : run Done 0 = 0.
Proof.
simplify.
equality.
Qed.

Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
Proof.
  simplify.
  equality.
Qed.


Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
Proof.
simplify.
equality.
Qed.
(* Define [numInstructions] to compute the number of instructions
 * in a program, not counting [Done] as an instruction.
 *)
Fixpoint numInstructions (p : Prog) : nat :=
  match p with 
    | Done => 0
    | AddThen e1 p1   => 1 + numInstructions (p1)
    | MulThen e1 p1   => 1 + numInstructions (p1)
    | DivThen e1 p1   => 1 + numInstructions (p1)
    | VidThen e1 p1   => 1 + numInstructions (p1)
    | SetToThen e1 p1 => 1 + numInstructions (p1)
  end.

Theorem numInstructions_Example :
  numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
Proof.
  simplify.
  equality.
Qed.

(* Define [concatProg] such that [concatProg p1 p2] is the program
 * that first runs [p1] and then runs [p2].
 *)
Fixpoint concatProg (p1 p2 : Prog) : Prog := 
  match p1 with
    | Done => p2
    | AddThen e1 res => AddThen e1 (concatProg res p2)
    | MulThen e1 res => MulThen e1 ( concatProg res p2)
    | DivThen e1 res => DivThen e1 ( concatProg res p2)
    | VidThen e1 res => VidThen e1 ( concatProg res p2)
    | SetToThen e1 res => SetToThen e1 (concatProg res p2)
  end.

Example a := concatProg (AddThen 1 Done) (MulThen 2 Done). 
Compute a.

Theorem concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
     = AddThen 1 (MulThen 2 Done).
Proof.
simplify.
equality.
Qed.

Theorem concat_base
  : forall (p1: Prog), concatProg p1 Done = p1.
Proof.
  simplify.
  induct p1; simplify; equality.
Qed.
(* Prove that the number of instructions in the concatenation of
 * two programs is the sum of the number of instructions in each
 * program.
 *)
Theorem concatProg_numInstructions
  : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                      = numInstructions p1 + numInstructions p2.
Proof.
simplify.
induction p1; simplify; equality; simplify; rewrite IHp1; equality.
Qed.
(* Prove that running the concatenation of [p1] with [p2] is
   equivalent to running [p1] and then running [p2] on the
   result. *)
Theorem concatProg_run
  : forall (p1 p2 : Prog) (initState : nat),
    run (concatProg p1 p2) initState =
    run p2 (run p1 initState).
Proof.
induct p1; simplify; equality.
Qed.
(* Read this definition and understand how division by zero is handled. *)
Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
  match p with
  | Done => (true, state)
  | AddThen n p => runPortable p (n+state)
  | MulThen n p => runPortable p (n*state)
  | DivThen n p =>
      if n ==n 0 then (false, state) else
      runPortable p (state/n)
  | VidThen n p =>
      if state ==n 0 then (false, 0) else
      runPortable p (n/state)
  | SetToThen n p =>
      runPortable p n
  end.
Arguments Nat.div : simpl never. (* you don't need to understand this line *)





Lemma run_portable_helper: forall (p: Prog) (n: nat),
  runPortable (DivThen 0 p) n = (false, n).
Proof.
  simplify.
  cases (n);simplify; equality.
Qed.

Lemma run_portable_helper_vid: forall (p: Prog) (n: nat),
  runPortable (VidThen n p) 0 = (false, 0).
Proof.
  simplify.
  cases (n);simplify; equality.
Qed.


Lemma run_portable_helper2: forall (p: Prog) (n n2: nat),
  n <> 0 -> runPortable (DivThen n p) n2 = runPortable p (n2 / n).
Proof.
  simplify.
  cases (n ==n 0).
  contradiction.
  equality.
Qed.


Lemma run_portable_helper_vid2: forall (p: Prog) (n n2: nat),
  n2 <> 0 -> runPortable (VidThen n p) n2 = runPortable p (n / n2).
Proof.
  simplify.
  cases (n2 ==n 0).
  contradiction.
  equality.
Qed.


Lemma run_portable_helper3: forall(p: Prog) (n s0 s1: nat),  
   (runPortable (DivThen n p) s0 = (true, s1)) -> n <> 0.
Proof.
intros.
cases n.
assert(H2: runPortable (DivThen 0 p) s0 = (false, s0)).
apply run_portable_helper.
rewrite H in H2.
equality.
linear_arithmetic.
Qed.

Lemma run_portable_helper_vid3: forall(p: Prog) (n s0 s1: nat),  
   (runPortable (VidThen n p) s0 = (true, s1)) -> s0 <> 0.
Proof.
intros.
cases s0.
assert(H2: runPortable (VidThen n p) 0 = (false, 0)).
apply run_portable_helper_vid.
rewrite H in H2.
equality.
linear_arithmetic.
Qed.


(* Prove that running the concatenation [p] using [runPortable]
   coincides with using [run], as long as [runPortable] returns
   [true] to confirm that no divison by zero occurred. *)
   
Lemma runPortable_run : forall p s0 s1,
  runPortable p s0 = (true, s1) -> run p s0 = s1.
Proof.
intros.
induct p; try(simplify; equality); try(apply IHp in H; simplify; try(rewrite plus_comm); try(rewrite mult_comm); try apply H).

apply IHp.
rewrite <- H.
rewrite run_portable_helper2.
equality.
assert(H2: runPortable (DivThen n p) s0 = (true, s1) -> n <> 0).
apply run_portable_helper3.
apply H2.
apply H.

apply IHp.
rewrite <- H.
rewrite run_portable_helper_vid2.
equality.
assert(H2: runPortable (VidThen n p) s0 = (true, s1) -> s0 <> 0).
apply run_portable_helper_vid3.
apply H2.
apply H.

Qed.

Fixpoint validate_helper p (b : bool) :=
    match p with
    | Done => true
    | AddThen n p => if n ==n 0 then validate_helper p b else validate_helper p true
    | MulThen n p => if n ==n 0 then validate_helper p false else validate_helper p b
    | DivThen n p => if n ==n 0 then false else (if b then validate_helper p (Nat.eqb n 1) else validate_helper p false)
    | VidThen n p => if b then validate_helper p false else false
    | SetToThen n p => if n ==n 0 then validate_helper p false else validate_helper p true
    end. 


Definition validate (p : Prog) : bool :=
  validate_helper p false.


(*Lemma validate_sound_helper: forall (p: Prog), validate p = true -> forall s, fst(runPortable p s) = true -> fst(runPortable p 0) = true.
induct p; simplify; try(apply IHp); try(equality).
unfold validate in IHp.
apply IHp.
Qed.*)


(*Lemma b : forall (p: Prog)(n: nat), fst (runPortable p (n)) = true <-> (runPortable p n = (true, run p n)).
Proof.
  induct p; simplify; try (apply IHp in H); try(rewrite <- plus_comm); try(rewrite <- mult_comm);
  try(equality); try(rewrite plus_comm in H); try(rewrite mult_comm in H); try(assumption);
  try(cases(n ==n 0); cases (n0 ==n 0));simplify; try(equality); try(rewrite IHp); try(equality).
Qed.

Lemma concat_portable : forall p1 p2 n, runPortable (concatProg p1 p2) n
        = (let (x, answer) := runPortable p1 n in if x then runPortable p2 answer else (x,answer)).
Proof.
  induct p1; try equality; simplify; try apply IHp1; try equality; try( cases (n ==n 0); cases (n0 ==n 0);
  try equality;
  simplify;
  apply IHp1).
Qed.
*)
  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
 * take a look at the hints for this pset on the course web site.
 * It is not expected that this pset is doable for everyone without the hints,
 * but some planning is required for successful proof.
 * In particular, repeatedly trying out different combinations of tactics
 * and ideas from hints until something sticks can go on for arbitrarily long
 * with little insight and no success; just guessing a solution is unlikely.
 * Thus, we encourage you to take your time thinking, look at the hints when
 * necessary, and only jump into coding when you have some idea why it should
 * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

(* The final goal of this pset is to implement [validate : Prog -> bool]
   such that if this function returns [true], the program would not trigger
   division by zero regardless of what state it starts out in.  [validate] is
   allowed to return [false] for some perfectly good programs that never cause
   division by zero, but it must recognize as good the examples given below.  In
   jargon, [validate] is required to be sound but not complete, but "complete
   enough" for the use cases defined by the examples given here: *)

Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
Example runPortable_good : forall n,
  runPortable goodProgram1 n = (true, 10/(1+n)).
Proof. simplify. equality. Qed.

Definition badProgram1 := AddThen 0 (VidThen 10 Done).
Example runPortable_bad : let n := 0 in
  runPortable badProgram1 n = (false, 0).
Proof. simplify. equality. Qed.


Definition badProgram2 := AddThen 1 (DivThen 0 Done).
Example runPortable_bad2 : forall n,
  runPortable badProgram2 n = (false, 1+n).
Proof. simplify. equality. Qed.

Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
Definition goodProgram4 := Done.
Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

(* If you already see a way to build [validate] that meets the
 * requirements above, _and have a plan for how to prove it correct_,
 * feel free to just code away. Our solution uses one intermediate definition
 * and one intermediate lemma in the soundness proof -- both of which are more
 * sophisticated than the top-level versions given here. *)
Example validate1 : validate goodProgram1 = true. Proof. equality. Qed.
Example validate2 : validate goodProgram2 = true. Proof. equality. Qed.
Example validate3 : validate goodProgram3 = true. Proof. equality. Qed.  
Example validate4 : validate goodProgram4 = true. Proof. equality. Qed.
Example validate5 : validate goodProgram5 = true. Proof. equality. Qed.
Example validate6 : validate goodProgram6 = true. Proof. equality. Qed.
Example validate7 : validate goodProgram7 = true. Proof. equality. Qed.
Example validate8 : validate badProgram1 = false. Proof. equality. Qed.
Example validate9 : validate badProgram2 = false. Proof. equality. Qed.


Lemma validate_sound_helper: forall p b, validate_helper p b = true ->
     forall s : nat, (b = true -> s <> 0) ->
     runPortable p s = (true, run p s).
induct p; try(simplify); try(equality).
rewrite plus_comm.
simplify.
cases (n ==n 0).
apply IHp with (b:=b).
assumption.
rewrite e.
simplify.
apply H0 in H1.
linear_arithmetic.
apply IHp with (b:=true).
assumption.
simplify.
linear_arithmetic.



rewrite mult_comm.
simplify.
cases (n ==n 0).
apply IHp with (b:=false).
assumption.
propositional.
equality.
apply IHp with (b:=b).
assumption.

simplify.
apply H0 in H1.
simplify.
apply Nat.neq_mul_0.
propositional.

cases (n ==n 0).
equality.
cases b.
apply IHp with (b:= Nat.eqb n 1).
assumption.
cases(Nat.eqb n 1). 
intros.
apply Nat.eqb_eq in Heq.
rewrite Heq.
apply H0 in H1.
rewrite Nat.div_1_r.
assumption.
propositional.
equality.
apply IHp with (b := false) (s := s/n).
assumption.
propositional.
equality.

cases (s ==n 0).
cases b.
propositional.
equality.
cases b.
apply IHp with (b := false) (s := n/s).
assumption.
propositional.
equality.
equality.

cases (n ==n 0).
apply IHp with (b := false) (s := n).
assumption.
propositional.
equality.

apply IHp with (b := true) (s := n).
assumption.
propositional.
Qed.

Hint Rewrite Nat.add_0_r.
Lemma validate_sound : forall p, validate p = true ->
  forall s, runPortable p s = (true, run p s).
Proof.
induct p; try(simplify); try(equality); try(rewrite plus_comm).
unfold validate in IHp.

apply validate_sound_helper with (s:=s) in H.
simplify.
assert(ejre: n + s = s + n).
linear_arithmetic.
rewrite <- ejre.
rewrite <- ejre in H.
trivial.
propositional.
equality.


apply validate_sound_helper with (s:=s) in H.
simplify.
assumption.
propositional.
equality.

cases (n ==n 0).
apply validate_sound_helper with (s:=s) in H.
simplify.
rewrite e in H.
simplify.
rewrite e.
apply H.
propositional.
equality.

apply validate_sound_helper with (s:=s) in H.
simplify.
cases (n ==n 0).
equality.
apply H.

propositional.
equality.

apply validate_sound_helper with (s:= s) in H.
simplify.
apply H.

propositional.
equality.

apply validate_sound_helper with (s:= s) in H.
simplify.
apply H.

propositional.
equality.
Qed.
(* Here is the complete list of commands used in one possible solution:
  - Search, for example Search (_ + 0).
  - induct, for example induct x
  - simplify
  - propositional
  - equality
  - linear_arithmetic
  - cases, for example cases (X ==n Y)
  - apply, for example apply H
  - apply in, for example apply H1 in H2 or apply somelemma in H1
  - apply with, for example apply H1 with (x:=2)
  - apply in with, for example apply H1 with (x:=2) in H2
  - rewrite, for example rewrite H
  - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
  - ;, for example simplify; propositional *)
