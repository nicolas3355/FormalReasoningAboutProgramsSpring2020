(** * Correctness of Binary Search Trees (BSTs) *)

(* Here we prove some correctness theorems about binary search trees (BSTs),
 * a famous data structure for finite sets, allowing fast (log-time) lookup,
 * insertion, and deletion of items. (We omit the rebalancing heuristics needed
 * to achieve worst-case log-time operations, but you will prove the correctness
 * of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Benjamin Sherman (sherman@csail.mit.edu), 
 * Andres Erbsen (andreser@mit.edu)
 *)

Require Import Frap Datatypes Pset4Sig.
Require Import Compare_dec.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

(* Trees are an inductive structure, where [Leaf] doesn't have any items,
 * whereas [Node] has an item and two subtrees. Note that a [tree] can
 * contain nodes in arbitrary order, so not all [tree]s are valid binary
 * search trees. *)
(* (* Imported from Sig file: *)
Inductive tree :=
| Leaf (* an empty tree *)
| Node (d : t) (l r : tree).
*)
(* Then a singleton is just a node without subtrees. *)
Definition Singleton (v: t) := Node v Leaf Leaf.

(* MOST IMPORTANT DEFINITION: *)
(* [bst] relates a well-formed binary search tree to the set of elements it
   contains. Note that invalid trees with misordered elements are not valid
   representations of any set. All operations on a binary tree are specified
   in terms of how they affect the set that the tree represents. That
   set is encoded as function that takes a [t] and returns the proposition "[t]
   is in this set". *)
Fixpoint bst (tr : tree) (s : t -> Prop) :=
  match tr with
  | Leaf => forall x, not (s x) (* s is empty set *)
  | Node d l r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
  end.
(* ^MOST IMPORTANT DEFINITION^ *)

(* [member] computes whether [a] is in [tr], but to do so it *relies* on the
   [bst] property -- if [tr] is not a valid binary search tree, [member]
   will (and should, for performance) give arbitrarily incorrect answers. *)
Fixpoint member (a: t) (tr: tree) : bool :=
  match tr with
  | Leaf => false
  | Node v lt rt =>
    match compare a v with
    | Lt => member a lt
    | Eq => true
    | Gt => member a rt
    end
  end.

(* Here is a typical insertion routine for BSTs.
 * From a given value, we recursively compare the value with items in
 * the tree from the root, until we find a leaf whose place the new value can take. *)
Fixpoint insert (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Singleton a
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (insert a lt) rt
    | Eq => tr
    | Gt => Node v lt (insert a rt)
    end
  end.


(* Helper functions for [delete] below. The *main task* in this pset
   is to understand, specify, and prove these helpers. *)
Fixpoint rightmost (tr: tree) : option t :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    match rightmost rt with
    | None => Some v
    | r => r
    end
  end.
(* Helper functions for [delete] below. The *main task* in this pset
   is to understand, specify, and prove these helpers. *)
Fixpoint leftmost (tr: tree) : option t :=
  match tr with
  | Leaf => None
  | Node v lt _ =>
    match leftmost lt with
    | None => Some v
    | l => l
    end
  end.
Definition is_leaf (tr : tree) : bool :=
  match tr with Leaf => true | _ => false end.
Fixpoint delete_rightmost (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    if is_leaf rt
    then lt
    else Node v lt (delete_rightmost rt)
  end.
Definition merge_ordered lt rt :=
  match rightmost lt with
  | Some rv => Node rv (delete_rightmost lt) rt
  | None => rt
  end.

(* [delete] searches for an element by its value, and removes it if it is found.
   Removing an element from a leaf is degenerate (nothing to do) and
   removing the value from a node with no other children (both Leaf) can be done
   by replacing the node itself with a Leaf. Deleting a non-leaf node is
   substantially trickier because the type of [tree] does not allow for a Node
   with two subtrees but no value -- merging two trees is non-trivial. The
   implementation here removes the value anyway, and then moves the rightmost
   node of the left subtree up to replace the removed value. This is equivalent
   to using rotations to move the value to be removed into leaf position and
   removing it there. *)
Fixpoint delete (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (delete a lt) rt
    | Eq => merge_ordered lt rt
    | Gt => Node v lt (delete a rt)
    end
  end.

(* Here is a lemma that you will almost definitely want to use. *)
Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
Proof.

  induct tr; simplify.
  { rewrite <-H0. apply H with (x:=x). }
  rewrite H0 in H.
  propositional.
  { apply IHtr1 with (P:=(fun x : t => P x /\ x < d)); propositional.
    { rewrite <-H0; trivial. }
    { rewrite H0; trivial. } }
  { apply IHtr2 with (P:=(fun x : t => P x /\ d < x)); propositional.
    { rewrite <-H0; trivial. }
    { rewrite H0; trivial. } }
Qed.

(* You may want to call these tactics to use the previous lemma. *)
(* They are just a means to save some typing of [apply ... with]. *)
Ltac use_bst_iff known_bst :=
  lazymatch type of known_bst with
  | bst ?tree2 ?set2 =>
      lazymatch goal with
      | |- bst ?tree1 ?set1 =>
          apply bst_iff with (P:=set2) (Q := set1);
          lazymatch goal with
          |- bst tree2 set2 => apply known_bst
          | _ => idtac
          end
      end
  end.
Ltac use_bst_iff_assumption :=
  match goal with
  | H : bst ?t _ |- bst ?t _ =>
    use_bst_iff H
  end.
(* If you are comfortable with it, [eapply bst_iff] followed by careful
 * application of other [bst] facts (e.g., inductive hypotheses) can
 * save typing in some places where this tactic does not apply, though
 * keep in mind that forcing an incorrect choice for a ?unification
 * variable can make the goal false. *)

(* It may also be useful to know that you can switch to proving [False] by
 * calling [exfalso]. This, for example, enables you to apply lemmas that end in
 * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

(* Other tactics used in our solution: apply, apply with, apply with in
 * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
   linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

(* Warm-up exercise: rebalancing rotations *)
(* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
   The AA-tree rebalancing algorithm applies these only if the annotations of relevant
   subtrees are in violation of a performance-critical invariant, but the rotations
   themselves are correct regardless. (These are straight from
   https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)
(* Each one can be written as a simple non-recursive definition
   containing two "match" expressions that returns the original
   tree in cases where the expected structure is not present. *)

Definition rotate (T : tree) : tree := 
  match T with
  | Leaf
  | Node _ _ Leaf => T
  | Node n_t l_a (Node n_r l_b r_x) => Node n_r (Node n_t l_a l_b) r_x
  end.

Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
Proof.
  cases T.
  equality.
  cases T2.
  equality.
  simplify.
  propositional; use_bst_iff_assumption; propositional; try equality; linear_arithmetic.

 (* + apply bst_iff with (Q:= (fun x : t => (s x /\ x < d0) /\ x < d)) in H.
    assumption.
    propositional.
    linear_arithmetic.
  
  + apply bst_iff with (Q:= (fun x : t => (s x /\ x < d0) /\ d < x)) in H1.
    equality.
    propositional.
  +

 *) 
Qed.
(* there is a hint on the class website that completely gives away the proofs
 * of these rotations. We recommend you study that code after completing this
 * exercise to see how we did it, and maybe pick up a trick or two to use below. *)

Lemma member_bst : forall tr s a, bst tr s -> member a tr = true <-> s a.
Proof.
  induct tr; simplify.
  + specialize (H a).
    propositional.
    equality.
  + cases (compare a d); propositional.
    - apply IHtr1 with (a := a) in H.
      propositional.
    - apply IHtr1 with (a := a) in H.
      propositional.
    - equality.
    - apply IHtr2 with (a := a) in H2.
      propositional.
    - apply IHtr2 with (a := a) in H2.
      propositional.
Qed.
Lemma bst_insert : forall tr s a, bst tr s ->
  bst (insert a tr) (fun x => s x \/ x = a).
Proof.
  induct tr; propositional.
  unfold insert.
  unfold Singleton.
  simplify.
  propositional; repeat (apply H in H0 || equality || linear_arithmetic).

  simplify.
  cases (compare a d); simplify.
  propositional.
  apply IHtr1 with (a := a) in H;
  
  (* repeat (use_bst_iff_assumption || propositional || linear_arithmetic);*)

  use_bst_iff_assumption.
  propositional.
  linear_arithmetic.
  use_bst_iff_assumption.
  propositional.
  linear_arithmetic.
  propositional.
  use_bst_iff_assumption.
  propositional; linear_arithmetic.
  use_bst_iff_assumption.
  propositional; linear_arithmetic.
  propositional.
  use_bst_iff_assumption.
  propositional; linear_arithmetic.


  apply IHtr2 with (a := a) in H2; (use_bst_iff_assumption; propositional; linear_arithmetic).
Qed.


(*
  if i have a bst tree s and i remove the right most then what will s look like?
  If i have a bst tree s and i add to the right most then what will will the new s be?

  if I insert an element that is bigger than all the members then i will add it to the rightmost.
  forall tr s a b, b > a -> bst tr s -> member a tr = true -> b = rigthmost tr.
*)

(* To prove [bst_delete], you will need to write specifications for its helper
   functions, find suitable statements for proving correctness by induction, and use
   proofs of some helper functions in proofs of other helper functions. The hints
   on the course website provide examples and guidance, but no longer ready-to-prove
   lemma statements. For time-planning purposes: you are not halfway done yet.
   (The Sig file also has a rough point allocation between problems.)

   It is up to you whether to use one lemma per function, multiple lemmas per
   function, or (when applicable) one lemma per multiple functions. However,
   the lemmas you prove about one function need to specify everything a caller
   would need to know about this function. *)
Definition map_op_def {A} (o : option t) (f : t -> A) (def : A) :=
  match o with
  | None => def
  | Some v => f v
  end.


(*Lemma delete_right_most_safe : forall t s,
  bst (delete_rightmost t) (map_op_def (rightmost t) (fun rm x => s x /\ x < rm) s)
  -> bst t s.
Proof.
  induction t.
  simplify.
  apply H.
  intros.
  cases t2.

  simplify.

  cases t2.
  - simplify.

  p`ropositional.
  a
  equality.

  
  cases t2.
  simplify.

  propositional.


  cases (rightmost t); simplify.
  simplify.
*)

Lemma test : forall x d,
  (x < d) \/ (d < x) <-> x <> d.
Proof.
  propositional.
  linear_arithmetic.
  linear_arithmetic.
  linear_arithmetic.
Qed.

Lemma test2 : forall t s d, bst t (fun x => s x /\ (x <> d)) <->  bst  t (fun x => s x /\ ((x < d) \/ (d < x))). 
Proof.
  simplify.
  rewrite iff_to_and.
  propositional.
  use_bst_iff_assumption.
  simplify.
  propositional; linear_arithmetic.
  use_bst_iff_assumption.
  simplify.
  propositional; linear_arithmetic.
Qed.

Lemma tyez :  forall t s d d0,  d < d0 -> bst t (fun x  => (s x /\ x < d0) /\ x < d) <-> bst t (fun x => (s x /\ x < d)).
Proof.
  simplify.
  rewrite iff_to_and.
  propositional.
  use_bst_iff_assumption.
  simplify.
  propositional; linear_arithmetic.
  use_bst_iff_assumption.
  simplify.
  propositional; linear_arithmetic.
Qed.

Lemma rightmost_elim: forall d l1 l2 n, rightmost (Node d l1 l2) = Some n -> rightmost l2 = Some n \/ n = d.
Proof.
simplify.
cases l2.
simplify.
assert (n = d) by equality.
equality.
cases (rightmost (Node d0 l2_1 l2_2)).
equality.
assert (n = d) by equality.
equality.
Qed.


Lemma sn: forall l s n, rightmost l = Some n -> bst l s -> s n. 
simplify.
induct l. simplify. try equality.
apply rightmost_elim in H.
simplify.
propositional.
apply IHl2 with (n:= n) in H3.
equality.
equality.
rewrite <- H2 in H1.
assumption.
Qed.

Lemma close_bst: forall d l r s, 
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x) <-> bst (Node d l r) s. 
Proof.
  simplify.
  equality.
Qed.
Lemma all_members_left_less_than_root: forall d l r s x, bst (Node d l r) s -> bst l  (fun x : t => s x /\ x < d) ->  (fun x : t => s x /\ x < d) x -> x < d.
simplify.
propositional.
Qed.

Lemma all_members_right_bigger_than_root: forall d l r s x, bst (Node d l r) s ->  bst r  (fun x : t => s x /\ d < x) ->  (fun x : t => s x /\ d < x) x -> x > d.
simplify.
propositional.
Qed.

Lemma is_leaf_true: forall tr, is_leaf tr = true -> tr = Leaf. 
Proof.
  induct tr; simplify; try equality.
Qed.


Lemma is_leaf_false: forall tr, is_leaf tr = false -> tr <> Leaf. 
Proof.
  induct tr; simplify; try equality.
Qed.
  
Lemma no_leaf: forall d l r, Node d l r <> Leaf.
Proof.
  equality.
Qed.

Lemma rightmost_lem: forall d l1 l2, l2 <> Leaf -> rightmost (Node d l1 l2) = rightmost l2.
Proof.
simplify.
cases l2.
equality.
simplify.
cases (rightmost l2_2).
equality.
equality.
Qed.

Lemma rightmost_lem': forall d l1 d2 l11 l22, rightmost (Node d l1 (Node d2 l11 l22)) = rightmost (Node d2 l11 l22).
Proof.
simplify.
cases l22.
equality.
simplify.
cases (rightmost l22_2).
equality.
equality.
Qed.


Lemma rightmost_isleaf: forall d l1 l2, l2 = Leaf -> rightmost (Node d l1 l2) = Some d.
Proof.
simplify.
cases l2.
equality.
simplify.
cases (rightmost l2_2).
equality.
equality.
Qed.

Lemma rightmost_final: forall d l1 l2, rightmost(Node d l1 l2) = rightmost l2 \/ rightmost (Node d l1 l2) = Some d.
Proof.
  intros.
  cases (is_leaf l2).
  apply is_leaf_true in Heq.
  apply rightmost_isleaf  with (d:=d) (l1:=l1) in Heq.
  propositional.

  apply is_leaf_false in Heq.
  apply rightmost_lem  with (d:=d) (l1:=l1) in Heq.
  propositional.
Qed.
 
Lemma tree_empty: forall l, rightmost l = None -> l = Leaf.
Proof.
  simplify.
  cases l.
  equality.
  cases (rightmost (Node d l1 l2)).
  equality.
  simplify.
  cases (rightmost l2).
  equality.
  equality.
Qed.


Lemma ho: forall d l r s n, rightmost l = Some n -> bst (Node d l r) s -> n < d. 
Proof.
  simplify.
  propositional.
  apply sn with (n:=n) in H0.
  propositional.
  assumption.
Qed.


Lemma ho': forall d l r s n, rightmost(Node d l r) = Some n -> bst (Node d l r) s -> n >= d. 
Proof.
  intros.
  specialize (sn _ _ _ H H0) as snn.
  cases r.
  simplify. 
  propositional.
  assert (d = n) by equality.
  linear_arithmetic.
  assert (H':=H).
  rewrite rightmost_lem' in H'.
  apply close_bst in H0.
  propositional.

  specialize (sn _ _ _ H' H3) as snn'.
  simpl in snn'.
  propositional.
  linear_arithmetic.
Qed.
(* Lemma forall tr s a, bst (Node d l1 l2) s -> s a -> a <= d *)
(* what happens to the s when i delete the rightmost of a tree? *)
(* if I delete the rightmost member n, then n will not be a member of the resulting s.*)
(* Lemma forall l s, bst l s -> delete_rightmost(l) -> s rightmost(l) -> False.*)
Lemma exists_a_not: forall l, is_leaf l = false -> exists n l1 l2, (Node n l1 l2) = l.
Proof.
  simplify.
  apply is_leaf_false in H.
  induct l.
  equality.
  eauto.
Qed.

  Lemma not_empty : forall l , exists n, is_leaf l = false ->  rightmost l = Some n.
Proof.
  simplify.
  cases l.
  exists 0.
  simplify.
  equality.
  
  intros.
  simplify.
  cases (rightmost l2).
  exists n.
  equality.
  exists d.
  equality.
Qed.


Lemma tree_not_empty : forall l n, rightmost l = Some n -> is_leaf l = false.
Proof.
  simplify.
  cases l.
  simplify.
  equality.
  equality.
Qed.

Lemma merge_with_leaf: forall tr2, merge_ordered Leaf tr2 = tr2.
Proof.
  equality.
Qed.

Lemma merge_with_leaf_imp: forall tr1, tr1 <> Leaf -> merge_ordered tr1 Leaf <> Leaf.
Proof.
  induct tr1.
  intros.
  equality.
  simplify.
  unfold merge_ordered.
  cases (rightmost (Node d tr1_1 tr1_2)).
  simplify.
  equality.
  apply tree_empty in Heq.
  equality.
Qed.


Lemma delete_rightmost_close : forall d l d2 l2 r2,
    delete_rightmost (Node d l (Node d2 l2 r2)) = (Node d l (delete_rightmost (Node d2 l2 r2))).
Proof.
  equality.
Qed.

Lemma ejre : forall tr1 s n, bst tr1 s ->  rightmost tr1 = Some n ->
bst (delete_rightmost tr1) (fun x : t => (s x /\ x < n)).
 Proof.

   induct tr1.
   simplify.
   equality.
   intros.
   cases (tr1_2).
   simpl.
   assert (H0' := H0).
   simpl in H0'.
   assert (Hb := H).
   simpl in H.
   propositional.
   use_bst_iff_assumption.
   propositional.
   assert (d = n) by equality.
   linear_arithmetic.

   assert (d = n) by equality.
   linear_arithmetic.
   rewrite delete_rightmost_close.
   rewrite <- close_bst.
   propositional.
   simplify.
   propositional.
   Check ho.
   Admitted.

  (* all_members_right_bigger_than_root *)
  (* all_members_left_less_than_root *)
Lemma member_less: forall s tr1 tr2 d x ,  bst (Node d tr1 tr2) s -> member x tr1 = true  -> x < d.  
Proof.
  intros.
  assert (H':=H).
  simplify.
  propositional.
  apply member_bst with (tr:= tr1) (s:= (fun x : t => s x /\ x < d))in H0. 
  propositional.
  assumption.
Qed.
  (* all_members_right_bigger_than_root *)
  (* all_members_left_less_than_root *)
Lemma member_more: forall s tr1 tr2 d x ,  bst (Node d tr1 tr2) s -> member x tr2 = true  -> x > d.  
Proof.
  intros.
  assert (H':=H).
  simplify.
  propositional.
  apply member_bst with (tr:= tr2) (s:= (fun x : t => s x /\ d < x)) in H0. 
  propositional.
  assumption.
Qed.


Lemma hi: forall tr n , rightmost tr = Some n -> (forall s, bst tr s -> (forall x, s x -> x <= n)).  
Proof.

  induct tr.
  simplify.
  equality.

  intros.

  assert (H2 := H).
  assert (H0b := H0).

  specialize (ho' d tr1  tr2  s n H2  H0b) as ho''. 
  cases tr2.
  2:{
  apply close_bst in H0b.
  propositional.
  rewrite rightmost_lem' in H.
  specialize (IHtr2 _ H _ H6).

  assert (x < d \/ x > d \/ x = d) by linear_arithmetic.

  cases(H4).
  linear_arithmetic.
  cases (H4).
  apply IHtr2.
  propositional.
  linear_arithmetic.
  }
  simplify.
  propositional.
  specialize (H7 x).
  propositional.
  linear_arithmetic.
Qed.

Lemma bst_delete : forall tr s a, bst tr s ->
  bst (delete a tr) (fun x => s x /\ x <> a).
Proof. 

  induction tr.
  + simplify.
    propositional.
    apply H in H1.
    contradiction.
  + simplify.
    cases (compare a d).
    - propositional.
      apply IHtr1 with (a := a) in H.
      simplify.
      repeat (use_bst_iff_assumption || propositional || linear_arithmetic).
    - clear IHtr1 IHtr2.
      propositional.
      rewrite <- e in *.
      clear e.
      unfold merge_ordered.
      cases (rightmost tr1).
      *
        simplify.
        propositional.
        ++ 
        apply sn with (s:=(fun x : t => s x /\ x < a)) in Heq; try (assumption); propositional; try assumption.
        ++ 
        apply ho with (d:=a) (r:= tr2) (s:=s) in Heq; try(linear_arithmetic); simplify; propositional; try assumption.
        ++
           assert (Heq':=Heq).
           apply ho with (d:=a) (r:= tr2) (s:=s) in Heq'; try (simplify; propositional).
           assert (bst (delete_rightmost tr1) (fun x : t => ((s x /\ (x < a)) /\ x < n))).
           +++ apply ejre; assumption.
           +++ use_bst_iff_assumption. simplify. propositional; try(linear_arithmetic).
       ++ 
           assert (Heq':=Heq).
           apply ho with (d:=a) (r:= tr2) (s:=s) in Heq'; try (simplify; propositional).
           use_bst_iff_assumption. simplify. propositional; try(linear_arithmetic).
           (*apply member_bst with (tr:= (Node a tr1 tr2)) in H1.*)
           simplify.
           cases (compare x a); try linear_arithmetic.
           +++
               apply hi with (x:=x) (s:= (fun x : t => s x /\ x < a)) in Heq.
               linear_arithmetic.
               assumption.
               propositional.
     *
      repeat (use_bst_iff_assumption || propositional || linear_arithmetic).
      apply tree_empty in Heq.
      rewrite Heq in H.
      simplify.
      specialize (H x).
      propositional.
      linear_arithmetic.
    
    - propositional.
      apply IHtr2 with (a := a) in H2.
      simplify.
      repeat (use_bst_iff_assumption || propositional || linear_arithmetic).
Qed.

(* Great job! Now you have proven all tree-structure-manipulating operations
   necessary to implement a balanced binary search tree. Rebalancing heuristics
   that achieve worst-case logarithmic running time maintain annotations on
   nodes of the tree (and decide to rebalance based on these). The implementation
   here omits them, but as the rotation operations are correct regardless of
   the annotations, any way of calling them from heuristic code would result in a
   functionally correct binary tree. *)

Lemma member_insert a tr s (H : bst tr s) : member a (insert a tr) = true.
Proof. eapply member_bst. eapply bst_insert. eapply H. right. congruence. Qed.
Lemma member_delete a tr s (H : bst tr s) : member a (delete a tr) = false.
Proof.
  assert(X:= bst_delete tr s a H).
  pose proof (bst_delete tr s a H) as X2.
  apply (member_bst _ _ a) in X.
  cases (member a (delete a tr)); propositional.
Qed.
