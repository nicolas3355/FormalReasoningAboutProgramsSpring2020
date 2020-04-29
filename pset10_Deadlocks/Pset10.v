(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 10 *)

(* Authors:
 * Adam Chlipala (adamc@csail.mit.edu),
 * Peng Wang (wangpeng@csail.mit.edu),
 * Samuel Gruetter (gruetter@mit.edu) *)

Require Import Frap Pset10Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset10Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Coq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog. Admitted.

(* FILL IN explanation here *)

(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset10Sig.v and briefly describing how it would
   reject it: *)
Lemma progPop: forall p x xs,
  x :: xs = progOf p -> exists y ys, (p = y :: ys) /\ snd y = x.
Proof.
  simplify.
  cases p.
  simplify.
  equality.
  exists p.
  exists p0.
  propositional; eauto.
  cases p.
  simplify.
  equality.
Qed.

Hint Resolve progPop : core.

Lemma progOfEmpty: forall p,
  [] = progOf p -> p = [].
Proof.
  simplify.
  cases p; eauto.
  cases p.
  simplify.
  equality.
Qed.

Hint Resolve progOfEmpty : core.

Lemma finished_no_locks : forall a,
  goodCitizen (fst a) (snd a) {} ->
  Forall finished (progOf [a]) -> locksOf [a] = {}.
Proof.
  intros.
  cases a.
  invert H0.
  simplify.
  invert H3.
  invert H.
  sets.
Qed.
 
(* FILL IN explanation here *)
Lemma finished_no_locks_l : forall p,
  Forall (fun h => goodCitizen (fst h) (snd h) {}) p
  -> Forall finished (progOf p)
  -> locksOf p = {}.
Proof.
  simplify.
  induct p; eauto.
  cases a.
  simplify.
  invert H0.
  invert H3.
  invert H.
  simplify.
  invert H2.
  replace ({ } \cup ({ } \cup locksOf p)) with (locksOf p) by sets.
  apply IHp; eauto.
Qed.

(*
Lemma step_cat' : forall h h' l l' (p: list (locks * cmd)) (a : cmd)(a':cmd),
   goodCitizen l a { } 
   -> Forall finished (progOf p)
   -> step0 (h, l, a) (h', l', a')
   -> exists h'', step (h, l \cup (locksOf p), a :: (progOf p)) (h'',l' \cup (locksOf p), a':: (progOf p)).
Proof.
  simplify.
  induct p.
  simplify.
  replace ({ } \cup l) with l by sets.
  replace (l' \cup { }) with l' by sets.
  eauto.
  cases a.
  simplify.
  invert H0.

  assert (p = []) by admit.
  subst.
  simplify.
  eauto.
  admit.
  invert H; simplify; eauto.
  eauto.
Qed.
*)
(* The two questions above are not graded, but we hope they help you understand
   the material better! *)
Lemma tyez: forall (x: locks * cmd) h res_locks,
   goodCitizen (fst x) (snd x) res_locks -> 
   finished (snd x) \/ (exists h_l_c' : heap * locks * cmd,
                                    step0 (h, fst x, snd x) h_l_c').
Proof.
  simplify.
  cases x.
  simplify.
  induct c; eauto; right.
  +
    invert H0.
    specialize (IHc h l2).
    propositional.
    invert H1.
    eauto.
    invert H1.
    cases x.
    cases p.
    eapply StepBindRecur in H0.
    eauto.
  + eexists; econstructor; invert H.
    specialize (H2 a).
    sets.
  + eexists; econstructor; invert H.
    sets.
Qed.

Theorem if_no_locks_held_then_progress : forall h p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> locksOf p = {}
      -> Forall (fun l_c => finished (snd l_c)) p
         \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  simplify.
  induct p; eauto.
  cases a.
  invert H.
  eapply tyez in H3.
  simplify.
  assert (s = {}) by sets.
  subst.
  assert (locksOf p = {}) by sets.
  rewrite H in *.
  propositional; simplify.
  + 
    left.
    econstructor.
    simplify.
    eauto.
    eauto.
  + invert H2.
    right.
    eapply step_cat.
    eassumption.
  + invert H1.
    cases x.
    cases p0.
    right.
    eexists.
    eapply StepThread1.
    eauto.
  + right.
    Check step_cat.
    invert H2.
    eapply step_cat in H3.
    invert H3.
    eauto.
Qed.

Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
Proof.
  simplify.
  induct c; eauto.
  + invert H0.
    eapply IHc in H6; eauto.
    propositional.
    - invert H0.
      right.
      left.
      eauto.
    - invert H3.
      invert H0.
      invert H3.
      right.
      left.
      eauto.
  + right; left.
    eauto.
  + right; left.
    eauto.
  + right.
    invert H.
    excluded_middle (a0 \in l).
    - eauto 10.
    - left.
      eauto.
  + right.
    invert H.
    eauto 10.
Qed.

 Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  simplify.
  assert (H':= H).
  eapply who_has_the_lock'' in H; eauto.
  cases H; eauto.
  right. invert H. invert H'. 
  sets.
Qed.

Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1.
  + simplify.
    sets.
  + cases x.
    simplify.
    cases H1.
    assert (H':=H).
    apply who_has_the_lock' with (h:=h) (a:= a) (l:=l) in H; eauto.
    2: sets.
    propositional.
    - left.
      invert H3.
      invert H.
      invert H3.
      eauto.
    - assert (locksOf l0 \subseteq l) by sets.
      propositional.
      invert H4.
      eauto.
Qed.

Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  simplify.
  induct bound; eauto.
  linear_arithmetic.
  assert (Hx := H).
  eapply who_has_the_lock in H; eauto.
  cases H.
  invert H.
  eauto.
  invert H.
  propositional.
  cases a; try linear_arithmetic.
  eapply IHbound in Hx; eauto.
Qed.

  
(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
 * reduces to proving this lemma. *)
Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  simplify.
  excluded_middle (exists a, a \in locksOf p).
  - invert H0.
    eapply if_lock_held_then_progress in H; eauto.
    propositional; eauto.
  - eapply if_no_locks_held_then_progress in H.
    2: {
      sets.
      assert (exists a, locksOf p a) by eauto.
      eauto.
    }
    propositional; eauto.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset10Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
