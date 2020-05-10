Require Import Frap Pset11Sig.

(* Part 1: read Pset11Sig.v and answer the questions below. This task is
 * ungraded, but we are assigning it in hope it helps you complete the
 * following parts.

(these are duplicative with past psets:)

- Which syntactic construct can be used to implement sequencing of two commands?

- Which step rules allow a sequenced program to make progress?

- Which step rule is used when a loop terminates?

- Which step rule is used when a loop continues?

- Why is there no step rule for Fail?

(these are about the programming language in this pset:)

- Which syntactic construct is used to spawn new threads?

- Which step rules allow a multi-threaded program to make progress?

- How can threads in this language communicate with each other?

- What do the steps that are factored out into the astep inductive have in common?

(these are about the program logic:)

- Which rule of the program logic handles astep commands?

- What is the meaning of the "rely" argument [R]?

- What would [R] be for a program that can run in any environment?

- What would [R] be for a program that can only run alone?

- Which constructors of [hoare_triple] change [R]? Do they make it more or less permissive?

- What is the meaning of the "guarantee" argument [G]?

- Which cases of [hoare_triple] require you to prove [G]?

- What would [G] be for a program that can run in any environment?

- What would [G] be for a program that can only run alone?

(these are about program logic tactics:)

- What syntactic forms of commands does [step] handle?

- What syntactic forms of commands does [fork] handle?

- What are the six arguments to the tactic [fork]? Classify them into two groups of three, and then (differently) classify them into three pairs.

- What syntactic forms of commands does [atomic] handle?

- What is the argument to the tactic [atomic]?
*)


(* Part 2: prove a program *)

(* Pset11Example.v constains an example verification of a non-trivial program.
 * You can use it as a reference when trying to figure out what the rules,
 * lemmas, and tactics here do, but you are not required to understand it.
 * The program in this file is much simpler. *)

(* Verify that this program manages to increase the counter value. *)
Lemma ht_increment : forall init,
  hoare_triple
    (fun h => h $! 0 = init)
    (fun _ _ => False)
    (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
     || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
    )
    (fun _ _ => True)
    (fun _ h => h $! 0 > init).
Proof.
  simp.
  fork
    (fun h => h$! 0 >= init)
    (fun (h: heap) (h': heap) => (h $!0 = h'$! 0) \/ h'$!0 > init )
    (fun (v: unit) h => h$! 0 > init)
    (fun h => h$! 0 >= init)
    (fun (h: heap) (h': heap) => (h $!0 = h'$! 0) \/ h'$!0 > init )
    (fun (v: unit) h => h$! 0 > init).
  all: simp.
  + eapply HtBind with (Q1 := (fun (v : nat) (h : heap) => v >= init));simp; eapply HtAtomic; simp.
  + eapply HtBind with (Q1 := (fun (v : nat) (h : heap) => v >= init));simp; eapply HtAtomic; simp.
Qed.


(* Part 3: prove soundness of the program logic *)

(* Now it remains to prove that having a [hoare_triple] actually means
 * that execution will proceed safely, and if the program terminates then the
 * postcondition will be satisfied. *)

(* If non-negligible time has passed since you read the sig file, please
 * review the definitions of [trsys_of] and [notAboutToFail] now. *)

(* Then, feel free to just skim the next lemmas, right until the final
 * theorem you are asked to prove. *)

(* Here are a few more lemmas that you may find helpful: *)

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof. eauto. Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', G h h' -> G' h h')
    -> hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma stableP_self : forall h R, stableP (fun h' => R^* h h') R.
Proof. simp. eauto using trc_trans. Qed.

Lemma stableP_star : forall R h h', R^* h h' ->
    forall P, stableP P R -> P h -> P h'.
Proof. induct 1; simplify; eauto. eapply IHtrc; eauto. Qed.

Lemma stableP_weakenR : forall P R, stableP P R -> forall R' : hrel,
    (forall h1 h2, R' h1 h2 -> R h1 h2) -> stableP P R'.
Proof. simp; eauto. Qed.

Hint Resolve stableP_self : core.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r,
  stable P Q R -> stableP (Q r) R.
Proof. unfold stable; propositional; eauto. Qed.
Hint Resolve stable_stableQ : core.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R,
  stable P Q R -> stableP P R.
Proof. unfold stable; propositional; eauto. Qed.
Hint Resolve stable_stableP : core.

Lemma trc_imply :forall t R (s s' : t), R^* s s' ->
  forall (R':_->_->Prop), (forall s s', R s s' -> R' s s') ->
  R'^* s s'.
Proof. induct 1; simplify; eauto. Qed.

Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Hint Constructors notAboutToFail : core.

Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        G^* h h'.
Proof.
  induct 1; simp.
  + invert H3; simp.
    eapply IHhoare_triple; eauto.
    econstructor.
  + invert H5; simp.
    ++ eapply H2 in H4.
       eapply IHhoare_triple1 in H8; eauto.
       eapply trc_imply; eauto.
    ++ eapply H3 in H4.
       eapply IHhoare_triple2 in H8; eauto.
       eapply trc_imply; eauto.
  + invert H1.
  + invert H3; simp; eauto.
  + invert H3; simp; eauto.
  + eapply H0 in H5.
    eapply IHhoare_triple in H6; simp.
    eapply trc_imply in H6; eauto.
Qed.

Lemma reverse_HtReturn: forall (A : Set) (P : hprop) (R : hrel) (v : A) G Q,
  hoare_triple P R (Return v) G Q
  -> stableP P R /\ (forall h, P h -> Q v h).
Proof.
  induct 1; simp; eauto.
Qed.

Proof.
Lemma preservation :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        hoare_triple (fun h'' => R^* h' h'') R c' G Q.
Proof.
  induct 1; simplify; simp.

  + 
    invert H3; simp.
    - econstructor; eauto.
    - apply reverse_HtReturn in H.
      propositional.
      econstructor; eauto.
      simplify.
      assert (P1 h).
      eapply stableP_star; eauto.
      eauto.
 +
      invert H5; simp.
      - econstructor; eauto; simp; eauto; simplify.
        ++ 
           eapply trc_imply; eauto.
        ++ 
           assert (Hx:=H4).
           apply H2 in H4.
           assert (H':=H).
           eapply always_stableP in H0.
           unfold stableP in H0.
           specialize (H0 h h').
           apply guarantee with (t:=_) (c:=c1)(R:=(fun h h' : heap => R h h' \/ G2 h h'))(G:=G1) (h:=h)(h':=h')(c':=c1') in H; eauto.
           assert(H'':= Hx).
           apply H3 in Hx.
           propositional.
           assert (G1 h h') by admit.
           propositional.
           apply H3.
           eapply stableP_star; eauto.
           admit.

      - econstructor; eauto; simp; eauto; simplify.
        ++ apply H2.
           admit.
        ++
           eapply trc_imply; eauto.

 + invert H1.
 + admit.
 + admit.
 + eapply HtConsequence; eauto; simp; eapply trc_imply; eauto.
Admitted.

Lemma progress :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h, P h ->
         notAboutToFail c.
Proof.
  induct 1; simp; eauto; econstructor; eauto.
Qed.


Theorem hoare_triple_sound : forall (t : Set) P (c : cmd t) Q,
  hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
  forall h, P h ->
  invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun prog => exists (P': hprop) (R': hrel), hoare_triple P' R' (snd prog) (fun _ _ : heap => True) Q /\ P' (fst prog)); eauto.
  +
    eapply invariant_induction; eauto.
    ++ simplify; propositional; cases s; simplify; assert(h=f)by equality; subst; eauto.
      assert (c=c0) by equality; subst; eauto.
    ++ simplify.
      cases s; cases s'; simp.
      eexists. eexists.
      propositional.
      eapply preservation; simplify; eauto.
      simplify.
      eauto.
  +
    simplify; simp; eapply progress; eauto.
Qed.

