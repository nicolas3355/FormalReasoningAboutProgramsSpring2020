(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 3 *)

Require Import Frap.Frap.
Require Import Pset3Sig.


(* Authors:
 * Ben Sherman (sherman@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Samuel Gruetter <gruetter@mit.edu>
 *)

(* In this pset, we will practice two topics:
   1) Polymorphic container types, i.e. types which are parametrized by a
      type, such as "option A", "list A", "tree A", and finally, "binary_trie A",
      which combines option and tree to obtain a new useful data structure.
   2) Higher-order functions (HOFs), i.e. functions which take other functions
      as arguments.
*)

(* Each of the exercises below is worth some number of points.
   If you just want to enjoy the proof hacking without getting distracted by points,
   feel free to ignore these points. On the other hand, if you want to know how
   many points each exercise earns you, you can find the points in Pset3Sig.v. *)


(** ****** Polymorphic container types ****** *)

(* First, we'll reproduce some definitions we need from Lecture 2,
   [tree] and [flatten]: *)

Inductive tree {A} :=
| Leaf
| Node (l : tree) (d : A) (r : tree).
Arguments tree : clear implicits.

Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.

(* And here's one additional definition that we'll use in this problem set.
 * [either] combines two [option] values into one.
 * If either argument to [either] is a [Some], then so is
 * the result of the [either], preferring the contents of
 * the first argument if both are [Some].
 *
 * We will observe an "analogy" between the [either]
 * function on options and the [++] function on lists.
 *)
Definition either {A} (xo yo : option A) : option A :=
  match xo with
  | None => yo
  | Some x => Some x
  end.

(* If we [either] an [option] value with [None]
 * on the right, it leaves that value unchanged,
 * (just as if we put the [None] on the left).
 * This is analogous to how appending [nil]
 * on either side of a list leaves it unchanged.
 *)
Theorem either_None_right : forall {A} (xo : option A),
    either xo None = xo.
Proof.
  simplify.
  cases xo; equality.
Qed.

Theorem either_None_left : forall {A} (xo : option A),
    either None xo = xo.
Proof.
  simplify.
  cases xo; equality.
Qed.


(* [either] is associative, just like [++]. *)
Theorem either_assoc : forall {A} (xo yo zo : option A),
    either (either xo yo) zo = either xo (either yo zo).
Proof.
  simplify.
  cases xo; cases yo; equality.
Qed.

(* [head] should compute the head of a list, that is,
 * it should return [Some] with the first element of
 * the list if the list is nonempty, and [None]
 * if the list is empty.
 *)
Definition head {A} (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: _ => Some x
  end.

Example head_example : head [1; 2; 3] = Some 1.
Proof.
  equality.
Qed.

(* The following theorem makes a formal connection
 * between [either] and [++].
 *)
Theorem either_app_head : forall {A} (xs ys : list A),
    head (xs ++ ys) = either (head xs) (head ys).
Proof.
  simplify.
  cases xs; try equality.
Qed.


(* [leftmost_Node] should compute the leftmost node of
 * a tree.
 *
 * Please implement [leftmost_Node] directly using
 * recursion (i.e., pattern matching) on the [tree] argument,
 * without using the [flatten] operation.
 *)
Fixpoint leftmost_Node {A} (t : tree A) : option A :=
  match t with
  | Leaf => None
  | Node Leaf d _ => Some d
  | Node l _ _ => leftmost_Node l
  end.  

Example leftmost_Node_example :
    leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf)
    = Some 2.
Proof.
  equality.
Qed.

Lemma jazz: forall {A} (l1: list A) (l2: list A) d, l1 ++ d :: l2 <> [].
Proof.
  simplify; cases l1; cases l2; simplify; try(equality).
Qed.

(* Prove that the leftmost node of the tree is the same
 * as the head of the list produced by flattening the tree
 * with an in-order traversal.
 *)
Theorem leftmost_Node_head : forall {A} (t : tree A),
    leftmost_Node t = head (flatten t).
Proof.
  simplify.
  induct t.
  simplify.
  try equality.
  cases (Node t1 d t2).
  equality.
  rewrite <- Heq.
  simplify.
  cases t1.
  simplify.
  equality.

  simplify.
  rewrite IHt1.
  simplify.
  unfold head.
  simplify.

  cases (flatten t1_1 ++ d1 :: flatten t1_2).
  assert(flatten t1_1 ++ d1 :: flatten t1_2 <> []).
  apply jazz.
  contradiction.
  equality.
Qed.

(* A binary trie is a finite map keyed by lists of Booleans.
 * We will implement a binary trie with entries of type [A]
 * by [tree (option A)]. The value at the root of the tree
 * corresponds to the entry for the key [nil : list bool],
 * the left subtree contains entries for those keys that
 * begin with [true], and the right subtree contains entries
 * for those keys that begin with [false].
 *)
Definition binary_trie A := tree (option A).

(* Define [lookup] such that [lookup k t] looks up the
 * map entry corresponding to the key [k : list bool] in the
 * binary trie [t : binary_trie A], interpreting [t] such that
 * the value at the root of [t] corresponds to the
 * entry for the key [nil], the left subtree contains entries
 * for those keys that begin with [true], and the right subtree
 * contains entries for those keys that begin with [false].
 *)

Definition get_root {A} (t : binary_trie A) : option A :=
 match t with
 | Leaf => None
 | Node _ root _ => root
 end.

Fixpoint lookup {A} (k : list bool) (t : binary_trie A) {struct t} : option A:=
  match t with
  | Leaf => None   
  | Node l d r =>
      match k with
      | [] => get_root t
      | b :: ks => lookup ks (if b then l else r)
      end
  end.

Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
Proof.
  equality.
Qed.

Example lookup_example2 : lookup [false; true]
    (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                          = Some 1.
Proof.
  equality.
Qed.

(* [Leaf] represents an empty binary trie, so a lookup for
 * any key should return [None].
 *)
Theorem lookup_empty {A} (k : list bool)
  : lookup k (Leaf : binary_trie A) = None.
Proof.
  equality.
Qed.

Check lookup [] (Node Leaf (Some(2)) Leaf).
Check lookup [] (Node (Node Leaf (Some 1) Leaf) (Some(2)) Leaf).
Check lookup [] (Node (Node Leaf (Some 2) Leaf) None ( (Node Leaf (Some 1) Leaf))).
Check lookup [] (Node (Node Leaf (Some 2) Leaf) (Some 2) (Node Leaf (None : option nat) Leaf)).
Check binary_trie.

(* Define an operation to "insert" a key and optional value
 * into a binary trie. The [insert] definition should satisfy two
 * properties: one is [lookup_insert] below, which says that if we
 * look up a key [k] in a trie where [(k, v)] has just been inserted,
 * the result should be [v]. The other is that lookups on keys different
 * from the one just inserted should be the same as on the original map.
 *
 * If an entry for that key already exists, [insert] should replace
 * that entry with the new one being inserted. Note that [insert] can
 * be used to remove an entry from the trie, too, by inserting [None]
 * as the value.
 *
 * Hint: it may be helpful to define an auxiliary function that inserts
 * a key and optional value into the empty trie.
 *)

Fixpoint insert_helper {A} (k : list bool) (v : option A): binary_trie A := 
  match k with 
    | [] => Node Leaf v Leaf 
    | b :: ks => if b then (Node (insert_helper ks v) (None: option A) Leaf) else (Node Leaf (None: option A) (insert_helper ks v))  
  end.
Compute insert_helper [true; true; true; true; true] (Some 3) .
Compute lookup[true; true; true; true] (insert_helper [true; true; true; true] (Some 3)).


Fixpoint insert {A} (k : list bool) (v : option A) (t : binary_trie A) {struct t}
  : binary_trie A := 
  match t with                                                                                       
    | Leaf => insert_helper k v
    | Node l d r => match k with
                  | [] => Node l v r
                  | b :: ks => 
                      if b 
                      then (Node (insert ks v l) d r)
                      else (Node l d (insert ks v r))
                  end
    end.

                  
Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
Proof.
  equality.
Qed.

Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
Proof.
  equality.
Qed.

Lemma insert_helper_is_correct {A}: forall k (v : option A), lookup k (insert_helper k v) = v.
Proof.
  induct k.
  equality.
  simplify.
  cases a; simplify; apply IHk.
Qed.

Theorem lookup_insert {A} (k : list bool) (v : option A) (t : binary_trie A) :
  lookup k (insert k v t) = v.
Proof.
  induct k.
  induct t.
  apply insert_helper_is_correct.
  simplify.
  equality.
  cases a.
  cases t.
  simplify.
  apply insert_helper_is_correct.
  simplify.
  apply IHk.
  simplify.
  cases t.
  simplify.
  apply insert_helper_is_correct.
  simplify.
  apply IHk.
Qed.

  
(** ****** Higher-order functions ****** *)

(* Recall the identity function [id] we used in class, which just returns its
   argument without modification: *)
Definition id {A : Type} (x : A) : A := x.

(* We also saw [compose], another higher-order function: [compose g f]
 * applies [f] to its input and then applies [g]. Argument order
 * follows the general convention of functional composition in
 * mathematics denoted by the small circle.
 *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

(* Let's use a small circle to refer to [compose]. This will make our
   goals much more readable.
   It's up to you to decide whether you also want to use the circle notation
   in your definitions, or whether you prefer to write "compose". *)
Notation " g ??? f " := (compose g f) (at level 40, left associativity).

Ltac hammer_unfold := repeat( 
                          unfold compose in *
                       || unfold id in *
                       || unfold map in *
                       || simplify
                       || equality
                       || linear_arithmetic
                     ).



(* Here are three simple properties of function composition. *)
Lemma compose_id_l : forall A B (f: A -> B),
    id ??? f = f.
Proof.
  hammer_unfold.
Qed.

Lemma compose_id_r : forall A B (f: A -> B),
    f ??? id = f.
Proof.
  hammer_unfold.
Qed.

Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
    h ??? (g ??? f) = h ??? g ??? f.
Proof.
  hammer_unfold.
Qed.

(* The selfCompose function takes a function and applies this function n times
   to the argument. There are different ways of defining it, but let's
   define it using only [id] and [compose]. *)
Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
  match n with
  | O => id
  | S n' => f ??? (selfCompose f n')
  end.

(* Here's an example of what [selfCompose] can do:
   If we apply the function which adds 2 to its argument 7 times to the starting
   value 3, we obtain 3 + 7 * 2 = 17. *)
Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17. Proof. equality. Qed.

(* We can also use [selfCompose] to define exponentiation on natural numbers, by
   saying "to raise [base] to the power [e], apply the function which multiplies
   its argument by [base] to [1] [e] times".
   Define [exp] using [selfCompose] and [Nat.mul]. *)
Definition exp(base e: nat): nat := 
selfCompose(Nat.mul base) e 1.

(* Once you define [exp], you can replace [Admitted.] below by [Proof. equality. Qed.] *)
Lemma test_exp_2_3: exp 2 3 = 8. Proof. equality. Qed. 
Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed. 
Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed. 
Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed. 
Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed. 

(* And here's another example to illustrate [selfCompose], make sure you understand
   why its result is 256. *)
Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256. Proof. equality. Qed.
Compute selfCompose (fun (x: nat) => x * x) 2 2.  

(* If we map the [id] function over any list, we get the
 * same list back.
 *)
Theorem map_id : forall {A : Type} (xs : list A),
    map id xs = xs.
Proof.
  hammer_unfold.
  induct xs; try(equality || rewrite IHxs; equality).
Qed.

(* If we map the composition of two functions over the list,
 * it's the same as mapping the first function over the whole list
 * and then mapping the second function over that resulting list.
 *)
Theorem map_compose : forall {A B C : Type} (g : B -> C) (f : A -> B) (xs : list A),
    map (g ??? f) xs = map g (map f xs).
Proof.
simplify.
induct xs; try(equality || rewrite IHxs; equality || hammer_unfold).
simplify.
f_equal.
apply IHxs.
Qed.

(* Just like we defined [map] for lists, we can similarly define
 * a higher-order function [tree_map] which applies a function on
 * elements to all of the elements in the tree, leaving the tree
 * structure intact.
 *)
Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
  : tree B :=
  match t with
  | Leaf => Leaf
  | Node l n r => Node (tree_map f l) (f n) (tree_map f r) 
  end.

Example tree_map_example :
  tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
  = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
Proof.
  equality.
Qed.


(* [tree_map_flatten] shows that [map]
 * and [tree_map] are related by the [flatten] function.
 *)
Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
    flatten (tree_map f t) = map f (flatten t).
Proof.
simplify.
induct t; simplify; try (equality).
rewrite IHt1.
rewrite IHt2.
rewrite <- map_cons.
rewrite map_app.
equality.
Qed.

(* *** Inverse functions *** *)

(* Using [compose] and [id], we can write a concise definition of when
   a function [g] is the inverse of a function [f]: *)
Definition inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := g ??? f = id.

(* Hint: In the following, it might be helpful to use the following fact:
   If two functions return the same value for all inputs, they are the same. *)
Check @FunctionalExtensionality.functional_extensionality.
(* Aside: I called it a "fact" above, but logicians disagree about whether
   we should believe this or not -- maybe you remember Adam's argument from
   class that even if merge sort and bubble sort return the same result for
   all inputs, they are two different things.
   Therefore, this "fact" is not actually built into Coq's kernel, but it's
   an axiom written down in the standard library, and if you believe in it,
   you can import it (the Frap library already does so).
   In any case, it is consistent with the rest of Coq's logic, i.e. by
   assuming this axiom, you will not be able to prove False, so we're safe.*)

(* Let's make a shorthand for this: *)
Definition fun_ext := @FunctionalExtensionality.functional_extensionality.

Ltac hammer_fun_ext_inv := repeat( 
                          unfold inverse in *
                      ||  apply fun_ext
                      ||  hammer_unfold
                     ).


Ltac hammer_prop := repeat (hammer_fun_ext_inv || propositional).

(* Here's an example: The function which subtracts two from its argument
   is the inverse of the function which adds two to its argument. *)
Example plus2minus2: inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
Proof.
  hammer_fun_ext_inv.
Qed.

Lemma fun_ext_rw : forall A B (f : A -> B) (g : A -> B), f = g 
                   <-> forall (x : A), f x = g x.
Proof.
  hammer_prop.
Qed.

(* On the other hand, note that the other direction does not hold, because
   if a subtraction on natural numbers underflows, it just returns 0, so
   there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
   so it can't have an inverse. *)
Example minus2plus2: ~ inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
Proof.
  hammer_fun_ext_inv.
  rewrite fun_ext_rw .
  apply Classical_Pred_Type.ex_not_not_all.
  exists 0.
  hammer_fun_ext_inv.
Qed.

(* The identity function is the inverse of itself.
   Note: we're using "@" in front of "id" to say "we want to provide all implicit
   type arguments explicitly, because otherwise Coq would not be able to infer them." *)
Lemma inverse_id: forall A, inverse (@id A) (@id A).
Proof.
  hammer_fun_ext_inv.
Qed.

(* Now we can start proving interesting facts about inverse functions:
   If g is the inverse of f, then [map g] is the inverse of [map f]: *)
Lemma invert_map : forall A B (f: A -> B) (g: B -> A),
    inverse f g ->
    inverse (map f) (map g).
Proof.
  simplify.
  unfold inverse in *.
  apply fun_ext.
  simplify.
  unfold compose.
  rewrite  <- map_compose .
  rewrite H.
  apply map_id.
Qed.



Lemma commutaive_selcompose{A: Type}: forall (g: A->A) n, g ??? selfCompose g n = selfCompose g n ??? g.
Proof.
  simplify.
  induct n.
  equality.
  simplify.
  rewrite IHn.
  rewrite  compose_assoc.
  f_equal.
  apply IHn.
Qed.

Hint Rewrite invert_map.
Hint Rewrite inverse_id.
(* And here's how to invert the power function: *)
Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
    inverse f g ->
    inverse (selfCompose f n) (selfCompose g n).
Proof.

  simplify.
  induct n.

  simplify.
  apply inverse_id.
  assert (H2 := H).
  apply IHn in H.

  simplify.
  unfold inverse in *.
  rewrite <- H.

  rewrite commutaive_selcompose.
  rewrite compose_assoc.
  f_equal.
  rewrite <- compose_assoc.
  rewrite H2.
  apply compose_id_r.
Qed.


(** ****** Optional exercises ******  *)


(* You've reached the end of the problem set. Congrats!
 *
 * If you're up for a completely optional additional challenge,
 * try defining a left-biased merge function below that merges two
 * binary tries, preferring map entries from the first binary trie
 * when an entry exists for both binary tries. Then prove
 * [lookup_left_biased_merge], which formally states that lookups
 * on the merged binary trie operate in exactly this manner.
 *
 * If you don't want to complete this additional challenge, you
 * can just leave everything below unmodified.
 *)

Fixpoint left_biased_merge {A} (t t' : binary_trie A) : binary_trie A :=
  match t with
  | Leaf => t'
  | Node l n r => match t' with
                  | Leaf => Node l n r
                  | Node l' n' r' => Node (left_biased_merge l l') (either n n') (left_biased_merge r r')
                  end
  end.
Theorem lookup_left_biased_merge_helper {A} (t t' : binary_trie A)(k: list bool) :
  lookup k (left_biased_merge t t') = either (lookup k t) (lookup k t').
Proof.
  induct t.
  induct t'.
  equality.
  equality.


  cases t'.
  simplify.
  rewrite  either_None_right.
  equality.

  cases k.
  simplify.
  equality.
  simplify.
  cases b.
  apply IHt1.
  apply IHt2.
Qed.


Theorem lookup_left_biased_merge {A} (k : list bool) (t t' : binary_trie A) :
  lookup k (left_biased_merge t t') = either (lookup k t) (lookup k t').
Proof.
  apply lookup_left_biased_merge_helper. 
Qed.

(* And here are a few more optional exercises about [fold]: *)

(* [fold] is a higher-order function that is even more general
 * than [map]. In essence, [fold f z] takes as input a list
 * and produces a term where the [cons] constructor is
 * replaced by [f] and the [nil] constructor is replaced
 * by [z].
 *
 * [fold] is a "right" fold, which associates the binary operation
 * the opposite way as the [fold_left] function that we defined
 * in lecture.
 *)
Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
         (xs : list A) : B :=
  match xs with
  | nil => b_nil
  | cons x xs' => b_cons x (fold b_cons b_nil xs')
  end.

(* For instance, we have
       fold plus 10 [1; 2; 3]
     = 1 + (2 + (3 + 10))
     = 16
 *)
Example fold_example : fold plus 10 [1; 2; 3] = 16.
Proof.
  simplify.
  equality.
Qed.

(* Prove that [map] can actually be defined as a particular
 * sort of [fold].
 *)
Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
    map f xs = fold (fun x ys => cons (f x) ys) nil xs.
Proof.
  simplify.
  induct xs.
  equality.
  simplify.
  f_equal.
  apply IHxs.
Qed.

(* Since [fold f z] replaces [cons] with [f] and [nil] with
 * [z], [fold cons nil] should be the identity function.
 *)
Theorem fold_id : forall {A : Type} (xs : list A),
    fold cons nil xs = xs.
Proof.
simplify.
induct xs.
equality.
simplify.
f_equal; apply IHxs.
Qed.

(* If we apply [fold] to the concatenation of two lists,
 * it is the same as folding the "right" list, and using
 * that as the starting point for folding the "left" list.
 *)
Lemma concat_with_empty: forall {A} (l :list A), l ++ [] = l. 
Proof.
induct l; simplify; try equality.
Qed.
Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                             (xs ys : list A),
    fold f z (xs ++ ys) = fold f (fold f z ys) xs.
Proof.
  simplify.
  induct xs; induct ys; simplify; try(equality).
  rewrite concat_with_empty.
  equality.
  simplify.
  specialize IHxs with (ys:= a0::ys).
  f_equal.
  rewrite IHxs.
  simplify.
  equality.
Qed.

(* Using [fold], define a function that computes the
 * sum of a list of natural numbers.
 *)
Definition sum : list nat -> nat :=
  fold plus 0.

Example sum_example : sum [1; 2; 3] = 6.
Proof.
  equality.
Qed.

(* Using [fold], define a function that computes the
 * conjunction of a list of Booleans (where the 0-ary
 * conjunction is defined as [true]).
 *)
Definition all : list bool -> bool := 
fold andb true.


Example all_example : all [true; false; true] = false.
Proof.
  equality.
Qed.


(* The following two theorems, [sum_append] and [all_append],
 * say that the sum of the concatenation of two lists
 * is the same as summing each of the lists first and then
 * adding the result.
 *)
Theorem sum_append : forall (xs ys : list nat),
    sum (xs ++ ys) = sum xs + sum ys.
Proof.
  simplify.
  unfold sum.
  induct xs.
  simplify.
  equality.
  simplify.
  rewrite IHxs.
  linear_arithmetic.
Qed.


Lemma l : forall a xs, all (a :: xs) = andb a (all xs).  
Proof.
  simplify; cases a; unfold all; equality.
Qed.

Theorem all_append : forall (xs ys : list bool),
    all (xs ++ ys) = andb (all xs) (all ys).
Proof.
  induct xs; simplify; try(equality).
  simplify. rewrite l.
  rewrite l. rewrite IHxs.
  rewrite andb_assoc.
  equality.
Qed.

(* Using [fold], define a function that composes a list of functions,
 * applying the *last* function in the list *first*.
 *)

(* Definition compose_list {A : Type} : list (A -> A) -> A -> A := *)
Definition compose_list {A : Type} (x: list (A -> A)) (y : A) : A :=
  fold (fun f g =>  f g) y x.
(* Fixpoint compose_list {A : Type} (x: list (A -> A)) (y : A) : A :=
   match x with
           |[]  => y
           |[x] => x y
           | x :: xs => x (compose_list xs y)
           end.*)


Example compose_list_example :
  compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
Proof.
  equality.
Qed.


(* Show that [sum xs] is the same as converting each number
 * in the list [xs] to a function that adds that number,
 * composing all of those functions together, and finally
 * applying that large composed function to [0].
 * Note that function [plus], when applied to just one number as an
 * argument, returns a function over another number, which
 * adds the original argument to it!
 *)
Theorem compose_list_map_add_sum : forall (xs : list nat),
    compose_list (map plus xs) 0 = sum xs.
Proof.
  induct xs; try(equality).
  unfold sum in *.
  unfold compose_list in *.
  simplify.
  rewrite IHxs.
  equality.
Qed.
