(** * 6.822 Formal Reasoning About Programs, Spring 2020 - Pset 2 *)

(*
Author: Samuel Gruetter <gruetter@mit.edu>

This PSet will introduce you to one of the major applications of formal reasoning
about programs: proving that an optimized program behaves the same as a simple program.

Imagine you're writing a program which needs a some function F. You know how to implement
F naively, but as you run your program, you notice that it spends a lot of time in
the function F. You find a library which claims to provide a very efficient implementation
of F, but looking at its source code, you don't really understand why this code should
calculate F, and you've seen some bug reports against previous versions of the library,
so you can't really know whether this library implements F correctly.
Since you care a lot about writing a correct program, you finally decide to keep using
your naive slow implementation.
Formal reasoning about programs to the rescue! If the authors of the library want to
increase the user's trust in their library, they can include the naive but simple-to-
understand version of F in their library as well, and write a proof that for all possible
inputs, the optimized version of F returns the same value as the simple version of F.
If that proof is in a machine-checkable format (e.g. in a Coq file), the library users do
not need to understand the implementation of the optimized F, nor the body of the proof,
but can still use the optimized F and be sure that it does the same as the simple
implementation, as long as they trust the proof checker.

In this PSet, we will put you in the role of the library author who writes a naive
version of F, an optimized implementation of F, and a proof that the two of them behave
the same.
*)


Require Import Coq.NArith.NArith. Open Scope N_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Frap.Frap.
Require Import Pset2Sig.
(* Set Default Goal Selector "!". *)

(* Each of the exercises below is worth some number of points.
   If you just want to enjoy the proof hacking without getting distracted by points,
   feel free to ignore these points. On the other hand, if you want to know how
   many points each exercise earns you, you can find the points in Pset2Sig.v. *)


(* Recursive functions *)
(* ******************* *)

(* We will need some recursive functions in this PSet. Defining recursive functions in Coq can be
   a bit tricky, because Coq only accepts recursive functions for which it believes that they always
   terminate.
   For natural numbers represented as "nat", and for data structures like the abstract syntax trees
   we saw in class, recursive functions can usually be defined using "Fixpoint", because each
   recursive call is with an argument which is a subterm of the original argument, which is required
   for Coq to be convinced that the recursive function terminates.
   In this pset, however, we will use the binary representation of natural numbers, which is
   called "N" in Coq. If we wanted to use a Fixpoint and call it with, e.g. the binary number
   11001101, we could only make recursive calls with 1001101.
   What we want in this Pset, however, is to make recursive calls with the one less than the argument,
   i.e. with 11001100 in this example.
   For this kind of recursion, which does not follow the structure of the data, we use the
   following pattern: *)

Definition fact: N -> N :=
  recurse by cases
  | 0 => 1
  | n + 1 => (n + 1) * recurse
  end.

(* This pattern can only define functions recursing over a natural number with base case 0, and
   one recursive case where the recursive call is for one less than the argument.
   The above function implements factorial, i.e. "fact n = 1 * 2 * ... * n".
   In the recursive case, you can use the word "recurse" to refer to the result of the recursive
   call. *)

(* Let's compute the first few values of fact: *)
Compute fact 0.
Compute fact 1.
Compute fact 2.
Compute fact 3.
Compute fact 4.

(* Aside: If you don't like the above Notation and want to see the real definition, you can do this:
Close Scope N_recursion_scope.
Print fact.
*)

(* Instead of writing "(fact x)" all the time, it's more convenient to just write "x!",
   so we make a Notation for this: *)
Local Notation "x !" := (fact x) (at level 12, format "x !").
(* Exercise: Define a simple exponentiation function in the same style,
   so that "exp base n" equals "base^n". *)

(*
Definition flip {A B C} (f : A -> B -> C) x y := f y x.
Definition exp: N -> N -> N :=
    flip (recurse by cases
    | 0 => (fun x => 1)
    | cheese + 1 => fun x => x * recurse x 
    end).
*)
Definition exp: N -> N -> N :=
  fun x =>
    recurse by cases
    | 0 => 1
    | _ + 1 => x * recurse
    end.



(* Once you define "exp", you can replace "Admitted." below by "Proof. equality. Qed." *)
Lemma test_exp_2_3: exp 2 3 = 8. Proof. equality. Qed. 
Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed. 
Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed. 
Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed. 
Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed. 

(* Here's another recursive function defined in the same style to apply a function f to
   a range of values:
   "seq f len start" computes the list [f start; f (start+1); ... f (start+len-1)] *)
Definition seq(f: N -> N): N -> N -> list N :=
  recurse by cases
  | 0 => fun start => []
  | n + 1 => fun start => f start :: recurse (start + 1)
  end.

Compute (seq (fun x => x * x) 4 0).

(* "ith i l" returns the i-th element of the list l.
   To understand the recursion, note that "ith i" returns a function which takes a list and,
   depending on whether i was 0 or not, returns the head of the list or the (i-1)-th element
   of the tail.
   If the index is out of bounds, it returns the default value 0. *)
Definition ith: N -> list N -> N :=
  recurse by cases
  | 0 => fun (l: list N) => match l with
                            | h :: t => h
                            | nil => 0
                            end
  | i + 1 => fun (l: list N) => match l with
                                | h :: t => recurse t 
                                | nil => 0
                                end
  end.

(* The standard library already contains a function called "length": *)
Check length.
(* However, it returns a "nat", i.e., the representation of natural numbers using O and S,
   which is very inefficient: To represent the number n, it needs roughly c*n bytes of RAM,
   where c is some constant, whereas "N", the binary representation of natural numbers,
   only used c*log(n) bytes of RAM.
   Therefore, we redefine our own length function which returns an N: *)
Fixpoint len(l: list N): N :=
  match l with
  | [] => 0
  | h :: t => 1 + len t
  end.
(* Note that since the recursion follows the structure of the data (the list) here,
   we use Fixpoint instead of "recurse by cases". *)

(* Here's a simple lemma: If we tell "seq" to return a list of length "count", it indeed does: *)
Lemma seq_len: forall f count start, len (seq f count start) = count.
Proof.
  induct count; simplify.
  - (* base case: count = 0 *)
    equality.
  - (* recursive case: assuming the statement holds for some "count", show that it
       also holds for "count + 1".
       This goal contains "seq f (count + 1) start", so we know that we're in the
       recursive case of "seq", so we'd like to replace "seq f (count + 1) start"
       by the recursive case we wrote in its definition.
       Unfortunately, neither "unfold seq" nor "simplify" can do this, but the
       tactic "unfold_recurse F k", where F is the function in question, and k
       its argument, does the job: *)
    unfold_recurse (seq f) count.
    (* And here's a hint you'll need later: Sometimes, your goal won't exactly contain
       (seq f (count + 1) start), but maybe (seq f someOtherExpression start), but you
       still know that someOtherExpression is strictly greater than 0.
       In such cases, if you want to use "unfold_recurse", you first have to run

       replace someOtherExpression with (someOtherExpression - 1 + 1) by linear_arithmetic.

       Note that if someOtherExpression could be 0, this won't work, because subtraction
       on natural numbers in Coq returns 0 if the result is negative, so "0 - 1 + 1"
       equals 1 in Coq's natural numbers, and linear_arithmetic can't prove "0 = 1"
       for you! *)

    simplify. rewrite IHcount. linear_arithmetic.
Qed.

(* An here's another general hint: You don't always need induction.
   Some lemmas in this pset can be solved using induction, but don't actually require it,
   and are simpler to solve if you don't use induction, so before doing induction,
   try to think where/if you would need an inductive hypothesis. *)

Compute ith 2 (seq (fun x => x * x) 4 0).
Compute (fun x => x * x)(0 + 2).
Compute (fun x => x *x)(1) :: seq (fun x => x*x) 3 (1+1).
Compute seq (fun x => x *x) 3 1.
(* (i=1, count =2, start 2).*)

Compute ith (1 + 1) (seq (fun x => x *x) (2 + 1) 2) = (fun x => x *x) (2 + (1 + 1)).
Compute ith (1 + 1) ((fun x => x *x) 2 :: seq (fun x => x *x) 2 (2 + 1)) = ith 1 (seq (fun x => x *x) 2 (2 + 1)).
(* Exercise: Prove that the i-th element of seq has the value we'd expect. *)

Lemma first_element: forall l a, ith 0 (a::l) = a.
Proof.
  simplify.
  equality.
Qed.

Lemma j: forall  i a l, i < len l -> ith (i + 1) (a :: l) = ith i (l).
induct i.
simplify.
equality.
simplify.
unfold_recurse (ith) (i+1).
equality.
Qed.

Lemma a: forall f count i start, i < count -> ith (i + 1) (f start :: seq f count (start + 1)) = ith i (seq f count (start + 1)).
Proof.
 induct i.
  simplify.
  equality.
  simplify.
  apply j.
  rewrite  seq_len.
  assumption.
Qed.
Lemma seq_spec: forall f count i start, i < count -> ith i (seq f count start) = f (start + i).
Proof.
  induct count; simplify. 
  apply N.nlt_0_r in H.
  equality.
  induct i.
  unfold_recurse (seq f) (count).
  simplify.
   f_equal. linear_arithmetic.


   assert(H2: (i + 1 < count + 1) <-> i < count).
   linear_arithmetic.
   apply H2 in H. 
   unfold_recurse (seq f) (count).
   rewrite a.


   rewrite   IHcount.
   f_equal.
   linear_arithmetic.
   assumption.
   assumption.
Qed.



Lemma concat: forall a l, len(a :: l) = 1 + len(l).
Proof.
  induct l; simplify; equality.
Qed.

Lemma empty: forall l, len l <= 0 -> l = [].
Proof.
  induct l.
  simplify.
  equality.
  rewrite concat.
  intros.
  cases l.
  simplify.
  linear_arithmetic.
  linear_arithmetic.
Qed.
(* Exercise: Prove that if the index is out of bounds, "ith" returns 0. *)
Lemma ith_out_of_bounds_0: forall i l, len l <= i -> ith i l = 0.
Proof.
induct i.
intros.
apply empty in H.
simplify.
rewrite H.
equality.
simplify.
induct l.
simplify.
unfold_recurse (ith) (i).
equality.
rewrite concat in H.

assert(H2: (1 + len l <= i + 1) -> len l <= i). 
simplify.
linear_arithmetic.
apply H2 in H.

apply IHi in H.
unfold_recurse (ith) (i).
assumption.
Qed.
(* Binomial coefficients *)
(* ********************* *)

(* You might remember binomial coefficients from you math classes, which appear in many combinatorics
   problems, and form the coefficients of the expansion of the polynomial (x + y)^n.
   In math notation, they are defined as follows:

      / n \        n!
      |   |  = ---------
      \ k /    (n-k)! k!

   We can transcribe this to Coq as follows: *)

Definition C(n k: N): N := n! / ((n - k)! * k!).

(* If we want to know how many ways there are to pick 2 items out of 4 items, we can compute this in Coq: *)
Compute C 4 2.

(* And here are the coefficients of the expansion of (x + y)^3: *)
Compute [C 3 0; C 3 1; C 3 2; C 3 3].

(* For larger numbers, however, this way of computing C becomes quite slow: If I do

Compute C 1000 100.

   it takes about 2 seconds on my computer. You can measure the time by putting "Time" in front of any command:

Time Compute C 1000 100.

   In the fraction defining C, there are many factors which appear both in the numerator and in the
   denominator, so it seems that we should be able to cancel these out and write a more efficient
   implementation of C. Here is one candidate: *)

Definition bcoeff(n: N): N -> N :=
  recurse by cases
  | 0 => 1
  | k + 1 => recurse * (n - k) / (k + 1)
  end.

(* Now if we do

Time Compute bcoeff 1000 100.

   it only takes about 0.02 seconds on my computer, so we got a 100x speed improvement, yay!
   But how do we know whether it's correct?
   We could do some quick tests: *)

Compute [bcoeff 3 0; bcoeff 3 1; bcoeff 3 2; bcoeff 3 3].

(* This test produces the same values as for C, but we want to be sure that bcoeff will *always* produce
   the same values as C, so let's prove it, i.e. let's show that

   forall n k, k <= n -> bcoeff n k = C n k

   We will do so further below, but we first need a few helper lemmas and techniques:

   Many arithmetic goals in this Pset are linear, i.e. we there are only multiplications by
   constants, but no multiplications of two variables.
   For these linear arithmetic goals, the linear_arithmetic tactic works just fine, but for
   some non-linear goals which will appear in this Pset, you can try the tactic "nia"
   (which stands for "non-linear integer arithmetic"), but it does not always work, so
   sometimes you will have to search for appropriate lemmas to apply manually.
   For instance, to prove the following: *)
Goal forall n m, n <> 0 -> m <> 0 -> n * m <> 0.
Proof.
  simplify.
  (* you could use the "Search" command with a pattern: *)
  Search (_ * _ <> 0).
  (* which outputs the name of a handy lemma we can apply: *)
  apply N.neq_mul_0.
  split; assumption.
  (* (note that in this case "nia" would have worked as well, but in any case, it's good to know
     the "Search" command. *)
Qed.

(* Here's another example of how to use the "Search" command:
   Suppose you have the goal *)
Goal forall n, n <> 0 -> n / n = 1.
Proof.
  simplify.
  (* If we do "Search (_ / _)" we get a very long list, but if we do *)
  Search (?x / ?x).
  (* we force the two numbers on both sides of the / to be the same, and we only get the lemma we need: *)
  apply N.div_same.
  assumption.
Qed.

(* Now we're ready to prove a few simple facts: *)

Lemma peal_fact: forall n, (n + 1)! = n! * (n+1).
Proof.
  simplify.
  unfold_recurse (fact) (n).
  apply N.mul_comm.
Qed.

Lemma fact_nonzero: forall n, n! <> 0.
Proof.
  induct n; simplify; try(equality).
  rewrite peal_fact.
  Search (_ * _ <> 0).
  apply N.neq_mul_0.
  split.
  apply IHn.
  linear_arithmetic.
Qed.

Lemma Cn0: forall n, C n 0 = 1.
Proof.
  induct n.
  compute.
  equality.
  Print C.
  unfold C.
  Search (?x - 0 = ?x).
  rewrite N.sub_0_r.
  assert(0! = 1).
  compute.
  equality.
  rewrite H.
  rewrite N.mul_1_r.
  apply N.div_same.
  apply fact_nonzero.
Qed.

Lemma Cnn: forall n, C n n = 1.
Proof.
  induct n.
  compute.
  equality.
  unfold C.
  simplify.
  Search (?x - ?x = 0).
  rewrite N.sub_diag.
  assert(0! = 1).
  compute.
  equality.
  rewrite H.
  Search (1 * ?x = ?x).
  rewrite N.mul_1_l.
  apply N.div_same.
  apply fact_nonzero.
Qed.
(* It's somewhat surprising that in the definition of C(n, k),

      n!
  -----------
  (n - k)! k!

  the denominator always divides the numerator.
  The following lemma proves it. Note that "(a | b)" means "a divides b".
  We provide the solution for you, so that you can step through it and use it as a
  source of useful strategies you can apply in the exercises below.
  Make sure to step through it and to understand each proof step! *)
Lemma C_is_integer: forall n k, k <= n ->
    (((n - k)! * k!) | n!).
Proof.
  induct n.
  - simplify.
    replace k with 0 by linear_arithmetic.
    simplify.
(* How can we prove that 1 divides 1? Probably it follows immediately from the definition of
   divisibility, so let's try to unfold it:

    unfold "|".

   Unfortunately that fails (reported at https://github.com/coq/coq/issues/11420), but we can do

    Locate "|".

   The output of this command shows us all notations involving "|", and the last one (N.divide) is the one
   we want. So we just unfold that one: *)
    unfold N.divide.
    exists 1. equality.
  - simplify. unfold N.divide in *.
    assert (k = 0 \/ k = n + 1 \/ 1 <= k <= n) as C by linear_arithmetic. cases C.
    + subst.
      replace (n + 1 - 0) with (n + 1) by linear_arithmetic.
      replace (0!) with 1 by equality.
      exists 1.
      linear_arithmetic.
    + subst.
      replace (n + 1 - (n + 1)) with 0 by linear_arithmetic.
      replace (0!) with 1 by equality.
      exists 1. linear_arithmetic.
    + pose proof (IHn k) as IH1.
      assert (k <= n) as A by linear_arithmetic. specialize (IH1 A). invert IH1.
      pose proof (IHn (k - 1)) as IH2.
      assert (k - 1 <= n) as B by linear_arithmetic. specialize (IH2 B). invert IH2.
      replace (n - (k - 1)) with (n - k + 1) in H1 by linear_arithmetic.
      unfold_recurse fact n.
      replace (k!) with ((k - 1 + 1)!) in *.
      2: { f_equal. linear_arithmetic. }
      unfold_recurse fact (k - 1).
      replace (k - 1 + 1) with k in * by linear_arithmetic.
      apply N.mul_cancel_r with (p := n - k + 1) in H0. 2: linear_arithmetic.
      apply N.mul_cancel_r with (p := k) in H1. 2: linear_arithmetic.
      assert (forall l1 r1 l2 r2, l1 = r1 -> l2 = r2 -> l1 + l2 = r1 + r2) as E. {
        simplify. linear_arithmetic.
      }
      specialize E with (1 := H0) (2 := H1).
      replace (n! * (n - k + 1) + n! * k) with ((n + 1) * n!) in E by nia.
      rewrite E.
      replace (n + 1 - k) with (n - k + 1) by linear_arithmetic.
      unfold_recurse fact (n - k).
      remember ((n - k)!) as F1.
      remember ((k - 1)!) as F2.
      remember (n - k + 1) as F3.
      remember k as F4.
      exists (x + x0).
      nia.
Qed.

(* Now we're ready to prove correctness of our optimized implementation bcoeff.
   Since this is not a class about math, we're providing a paper proof of each proof step
   of the inductive case:

  C(n, k + 1)

             n!
= -----------------------
  (n - (k + 1))! (k + 1)!

             n!
= -----------------------
  (n - k - 1)! k! (k + 1)

         n! (n - k)
= -------------------------------
  (n - k - 1)! (n - k) k! (k + 1)

               n! (n - k)
= ---------------------------------------
  (n - k - 1)! (n - k - 1 + 1) k! (k + 1)

          n! (n - k)
= ---------------------------
  (n - k - 1 + 1)! k! (k + 1)

      n! (n - k)
= -------------------
  (n - k)! k! (k + 1)

  n! (n - k)
= ----------- / (k + 1)
  (n - k)! k!

      n!
= ----------- * (n - k) / (k + 1)
  (n - k)! k!

= C(n, k) * (n - k) / (k + 1)

= bcoeff(n, k) * (n - k) / (k + 1)

= bcoeff(n, k + 1)

Your task is to translate this proof into Coq!

Potentially useful hint:
Note that multiplication and division have the same operator priority, and both are left-associative, so
   "a / b * c / d" is "((a / b) * c) / d", NOT "(a / b) * (c / d)"

Here we go: *)
Lemma bcoeff_correct: forall n k, k <= n -> bcoeff n k = C n k.
Proof.
  induct k.
  simplify.
  rewrite Cn0.
  equality.

  simplify.
  symmetry.
  unfold C.

  rewrite peal_fact.
  Search ((?c * _ )/ (?c * _)).
  (* N.div_mul_cancel_l. *)
  assert (H2 : (n-k) * (n!) / ((n-k) * ((n - (k + 1))! * (k! * (k + 1)))) = (n! / ((n - (k + 1))! * (k! * (k + 1)))) ).
  assert (H3: (n - k) <> 0).
  linear_arithmetic.
  rewrite  N.div_mul_cancel_l with (c:= (n - k)).
  equality.
  Search (_ * _ <> 0).
  apply N.neq_mul_0.
  split.
  apply fact_nonzero with (n:= (n - (k + 1))).
  apply N.neq_mul_0.
  split.
  apply fact_nonzero.
  linear_arithmetic.
  assumption.
  rewrite <- H2.


  assert((n - k) * (n - (k + 1))! = (n - k)!).
  assert( n - (k + 1) = n - k - 1) by linear_arithmetic.
  rewrite H0.
  replace (n - k)  with ((n - k - 1 + 1))  by linear_arithmetic.
  replace (n - k - 1 + 1 - 1) with (n- k - 1) by linear_arithmetic.
  symmetry.
  Search (?a * ?b = ?b * ?a).
  rewrite <- N.mul_comm.
  apply  peal_fact with (n := (n - k - 1)).
  rewrite N.mul_comm.
  replace ((n - k) * ((n - (k + 1))! * (k! * (k + 1)))) with ((n - k) * (n - (k + 1))! * (k! * (k + 1))) by linear_arithmetic. 
  rewrite H0.
  replace ((n - k)! * (k! * (k + 1))) with ((n - k)! * k! * (k + 1)) by linear_arithmetic.
  replace ((n - k)! * k! * (k + 1))with (((n - k)! * k!) * (k + 1)) by linear_arithmetic.
  rewrite N.mul_comm.
  
  assert (H3: ((n - k) * n! / ((n - k)! * k! * (k + 1))) = ((n - k) * n! / ((n - k)! * k!) / (k + 1))).
  rewrite <-  N.div_div.
  equality.
  apply N.neq_mul_0;split;apply fact_nonzero.
  linear_arithmetic.
  rewrite H3.



rewrite N.divide_div_mul_exact with (c:= (n - k)) (a:= n!) (b:=((n - k)! * k!)). 
replace  ((n! / ((n - k)! * k!))) with (C n k) by equality.
rewrite N.mul_comm.
rewrite <- IHk.
unfold_recurse (bcoeff n) (k).
equality.
linear_arithmetic.
apply N.neq_mul_0;split;apply fact_nonzero. 
apply C_is_integer.
linear_arithmetic.
Qed.


(* All binomial coefficients for a given n *)
(* *************************************** *)

(* In some applications, we need to know all binomal coefficients C(n,k) for a fixed n.
   For instance, if we want to symbolically evaluate (x + y)^4, the result is

   C(4,0)*x^4 + C(4,1)*x^3*y + C(4,2)*x^2*y^2 + C(4,3)*x*y^3 + C(4,4)*y^4

   The simplest way to compute such lists would be to just use the C we defined above: *)

Definition all_coeffs_slow1(n: N): list N :=
  (recurse by cases
   | 0 => [1]
   | k + 1 => C n (k + 1) :: recurse
   end) n.

Compute C 4 2.
Compute all_coeffs_slow1 0.
Compute all_coeffs_slow1 1.
Compute all_coeffs_slow1 2.
Compute all_coeffs_slow1 3.
Compute all_coeffs_slow1 4.
Compute all_coeffs_slow1 5.
Compute all_coeffs_slow1 15.
(* However, this is not very efficient:

Time Compute all_coeffs_slow1 100.

takes 0.8s on my machine *)

(* We could use our more efficient bcoeff from above: *)
Definition all_coeffs_slow2(n: N): list N :=
  (recurse by cases
   | 0 => [1]
   | k + 1 => bcoeff n (k + 1) :: recurse
   end) n.

Compute all_coeffs_slow2 5.
Compute all_coeffs_slow2 15.
(* This is faster:

   Time Compute all_coeffs_slow2 100.

takes 0.2s on my machine and

  Time Compute all_coeffs_slow2 200.

takes 1.7 s on my machine.

But we can do even better by using Pascal's triangle:

      1
     1 1
    1 2 1
   1 3 3 1
  1 4 6 4 1

You can observe that the i-th row of this triangle is the result of "all_coeffs_slow1 i",
and that each value not at the boundary of the triangle is the sum of the values to
its upper left and its upper right. For instance, the 6 in the last row is the sum of the
two 3s above it.
More formally, we can state this as follows: *)
Definition Pascal's_rule: Prop := forall n k,
    1 <= k <= n ->
    C (n+1) k = C n (k - 1) + C n k.
(* Note that the above is only a definition which gives a name to this proposition,
   but not a lemma.
   We don't ask you to prove it, but it's a fun optional exercise, have a look at the
   end of this file if you're interested! *)

(* The following function takes in a line of Pascal's triangle and computes the line below it: *)
Definition nextLine(l: list N): list N :=
  1 :: seq (fun k => ith (k - 1) l + ith k l) (len l) 1.

Compute nextLine [1; 3; 3; 1].
Compute nextLine (nextLine [1; 3; 3; 1]).

(* This allows us to define a faster all_coeffs function: *)
Definition all_coeffs_fast: N -> list N :=
  recurse by cases
  | 0 => [1]
  | n + 1 => nextLine recurse
  end.

(* Time Compute all_coeffs_fast 200. takes 0.35s on my computer *)


Lemma helper_len: forall a l, len(a::l) = 1 + len l.
induct l; simplify; equality.
Qed.

Lemma length_all_coeffs: forall n, len(all_coeffs_fast(n)) = n + 1.

induct n.
simplify.
linear_arithmetic.
simplify.
unfold_recurse all_coeffs_fast n.
unfold nextLine.
rewrite helper_len.
rewrite seq_len.
rewrite IHn.
linear_arithmetic.
Qed.

Hint Rewrite Cnn.
Hint Rewrite length_all_coeffs.
Hint Rewrite helper_len.
Hint Rewrite seq_len.
Ltac hammer:= repeat (simplify; try linear_arithmetic; simplify; try equality; simplify).

(* Exercise: Let's prove that all_coeffs_fast is correct.
   Note that you can assume Pascal's rule to prove this. *)
Lemma all_coeffs_fast_correct:
  Pascal's_rule ->
  forall n k,
    k <= n ->
    ith k (all_coeffs_fast n) = C n k.
Proof.
induct n.
simplify.
cases k.
equality.
linear_arithmetic.


simplify.
unfold_recurse all_coeffs_fast n.
unfold nextLine.

induct k.
rewrite first_element.
rewrite Cn0.
equality.

clear IHk.
assert(k <= n) by linear_arithmetic.

rewrite j; hammer.
rewrite seq_spec; hammer.
replace (1 + k - 1) with k  by linear_arithmetic.
replace (1 + k) with (k + 1) by linear_arithmetic.
rewrite IHn; hammer.
unfold Pascal's_rule in H.
assert (k < n \/ k = n) by linear_arithmetic.
cases H2.
rewrite IHn; hammer.
rewrite H; hammer.
replace (k + 1 - 1) with k  by linear_arithmetic.
equality.
rewrite ith_out_of_bounds_0; hammer.
rewrite H2; hammer.
Qed.

(* ----- THIS IS THE END OF PSET2 ----- All exercises below this line are optional. *)
(* Optional exercise: Let's prove that Pascal's rule holds.
   On paper, this can be proved as follows, but feel free to ignore this if you want
   the full challenge!

   C(n, k-1) + C(n, k)

           n!                 n!
= --------------------- + -----------
  (n - k + 1)! (k - 1)!   (n - k)! k!

              n!                          n!
= ----------------------------- + -------------------
  (n - k)! (n - k + 1) (k - 1)!   (n - k)! k (k - 1)!

               n! k                          n! (n - k + 1)
= ------------------------------- + -------------------------------
  (n - k)! (n - k + 1) (k - 1)! k   (n - k)! k (k - 1)! (n - k + 1)

         n! (k + n - k + 1)
= -------------------------------
  (n - k)! (n - k + 1) (k - 1)! k

    (n + 1)!
= ---------------
  (n - k + 1)! k!

= C(n+1, k)
*)
Lemma Pascal's_rule_holds: Pascal's_rule.
Proof.
  unfold Pascal's_rule.

  (* Note: Proving
       a     b     a+b
      --- + --- =  ---
       c     c      c
     is a bit trickier than you might expect, because we're using integer division here.
     So, for instance,
      1     3                                                              1+3
     --- + ---   equals 0 + 1 in round-down integer division, which is not ---
      2     2                                                               2
     To make sure this rule holds, we must also require that c and b both divide a: *)
  assert (forall a b c, c <> 0 -> (c | a) -> (c | b) -> a / c + b / c = (a + b) / c)
    as add_fractions. {
    clear.
    simplify.
    unfold N.divide in *. invert H0. invert H1.
    rewrite N.div_mul by assumption.
    rewrite N.div_mul by assumption.
    replace (x * c + x0 * c) with ((x + x0) * c) by nia.
    rewrite N.div_mul by assumption.
    reflexivity.
  }

Admitted.


(* Optional exercise:
   all_coeffs_fast is still not as fast as it could be, because nextLine uses ith
   to access the elements of the previous line, and each invocation of ith takes
   linear time in i.
   It would be more efficient to implement nextLine as a recursive function
   which iterates through the previous line just once and computes the next line
   on the fly.
   Define such a nextLine' function, and then use it to define all_coeffs_faster,
   observe how it's even faster than all_coeffs_fast, and finally, prove that
   it's correct. *)

Definition nextLine'(l: list N): list N. Admitted.

Definition all_coeffs_faster: N -> list N. Admitted.

Lemma all_coeffs_faster_correct: forall n k,
    k <= n ->
    ith k (all_coeffs_faster n) = C n k.
Proof.
Admitted.
