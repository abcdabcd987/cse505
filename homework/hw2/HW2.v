(** * CSE505 - HW2 *)

(*
 * Throughout, we include the approximate lines of code (LOC) or number of tactics
 * for each of our solutions to these problems. These are rough guidelines to help
 * you figure out if you are getting off-track; there is no penalty for
 * writing a shorter or longer solution.
 *)

Require Import Frap HW2Sig.
Open Scope string_scope. (* lets you use the "" syntax for strings *)

(* --- Part 1: String programs --- *)

(* In this assignment, we will work with a simple language
 * of string programs.

 * The [Prog] datatype defines abstract syntax trees for this language.
 * See HW2Sig for details.
 *)

Print Prog.

(* We will implement the run function and prove some properties about it.
 * First, we will define a few functions on strings.
 * These functions may be useful for your run function, but it is OK if you
 * do not use them.
 *
 * The string datatype in Coq is implemented as a custom list of characters:
 *)

Print string.

(* Problem 1 [10 points, ~5 LOC]: Implement the `repeat` function, which repeats a
   string n times. If n is 0, this should return the empty string.
   For example, repeat "foo" 3 = "foofoofoo".

   Hint: You may want to use the string `append` function, which
   has the notation ++. *)
Fixpoint repeat (s : string) (n : nat) : string :=
  "". (* your code here *)

(*
 * Tests for problem 1:
 *)
Theorem repeatTest1:
  repeat "foo" 3 = "foofoofoo".
Proof.
  (* your code here *)
Admitted. (* change to QED *)

Theorem repeatTest2:
  forall s, repeat s 0 = "".
Proof.
  (* your code here *)
Admitted. (* change to QED *)

Theorem repeatTest3:
  repeat "bar" 1 = "bar".
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(* Problem 2 [10 points, ~5 LOC]: Write a function `reverse` that reverses a string.
 *
 * Hint: The list reverse function `rev` might be a helpful reference.
 *)
Fixpoint reverse (s : string) : string :=
  "". (* your code here *)

(*
 * Tests for problem 2:
 *)
Theorem revTest1:
  reverse "cse505" = "505esc".
Proof.
  (* your code here *)
Admitted. (* change to QED *)

Theorem revTest2:
  reverse "" = "".
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(*
 * We will now define what it means to run a program.
 *)

(* Problem 3 [15 points, ~7 LOC]: Define [run] such that [run p] computes the string that
 * running the program [p] should result in. See the comments in the definition of
 * Prog in HW2Sig.v as well as the examples below for details.
 *
 * Hint: The functions you have just defined and the string `append` function ++
 * may be useful (but it is OK if you do not use them).
 *)
Fixpoint run (p : Prog) : string :=
  "". (* your code here *)

(*
 * Tests for problem 3:
 *)
Theorem run_Example1:
  run (Const "foo") = "foo".
Proof.
  (* your code here *)
Admitted.

Theorem run_Example2:
  run (Add (Const "1") (Const "2")) = "12".
Proof.
  (* your code here *)
Admitted.

Theorem run_Example3:
  run (Rev (Mul (Const "12") 3)) = "212121".
Proof.
  (* your code here *)
Admitted.

(* Next, we can prove some properties about the running the program.
 * We will prove that running a program preserves the length of the expressions.
 * That is, the length of the string that running the program produces is the same
 * as the sum of the lengths of all of the subexpressions together.
 *
 * First, we will prove some lemmas about strings.
 * These lemmas were helpful for our preservation proof, but
 * it is OK if you do not need to use them in your final proof.
 *)

(*
 * Problem 4 [10 points, ~6 tactics]: Prove that the length of the result of appending
 * two strings is the same as the sum of the lengths of each string.
 *
 * Hint: You may want to use some of the tactics: induction, rewrite, and/or f_equal.
 *)
Lemma len_app_plus:
  forall s1 s2,
    String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(*
 * Problem 5 [10 points, ~6 tactics]: Prove that the length of repeating a string n times
 * is n times the length of the string.
 *)
Lemma len_repeat:
  forall s n,
    String.length (repeat s n) = n * String.length s.
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(*
 * Problem 6 [10 points, ~8 tactics]: Prove that the length of reversing a string is the
 * same as the length of the string.
 *
 * Hint: The ring tactic can take care of some rewriting of mathematical expressions.
 *)
Lemma len_rev:
  forall s,
    String.length (reverse s) = String.length s.
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(*
 * With one more definition, we can define and prove the theorem:
 *)

(* The sum of the lengths of subexpressions *)
Fixpoint sub_len (p : Prog) : nat :=
  match p with
  | Const s => String.length s
  | Add p1 p2 => sub_len p1 + sub_len p2
  | Mul p' n => n * sub_len p'
  | Rev p' => sub_len p'
  end.

(*
 * Problem 7 [20 points, ~12 tactics]: Show that running a program preserves the
 * length of the subexpressions.
 *
 * Hint: You may want to use the lemmas you just defined (but it is OK if you do not).
 *)
Theorem run_pres_len:
  forall p,
    String.length (run p) = sub_len p.
Proof.
  (* your code here *)
Admitted. (* change to QED *)

(* --- Part 2: A common problem in Coq --- *)

(*
 * As discussed in a message board post last week
 * (http://groups.google.com/a/cs.washington.edu/forum/#!topic/cse505-18au-discussion/pKcmQ2uRDm8),
 * the order in which you introduce variables in Coq can impact whether or not
 * it is possible to finish an inductive proof. This is an instance
 * of a more general problem where the inductive hypothesis is sometimes
 * not strong enough to prove your goal. In such a case, you need to
 * strengthen the inductive hypothesis (for example, by waiting to introduce
 * a variable until later, or by proving a lemma with a stronger conclusion
 * and using that lemma to prove your goal).
 *
 * Most Coq users first encounter this problem in a pretty awful way
 * by spending hours on a proof that actually isn't possible. To hopefully save
 * you this pain, we're going to introduce this problem in an environment
 * where you know it will occur.
 *
 * The code below and the problem that we use for this is taken from a blog post by James Wilcox:
 * http://homes.cs.washington.edu/~jrw12/InductionExercises.html
 * Some of the accompanying text is also from this blog post.
 *)

(* add a list of natural numbers *)
Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

(* tail-recursive version of sum *)
Fixpoint sum_tail' (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => sum_tail' xs (x + acc)
  end.

Definition sum_tail (l : list nat) : nat :=
  sum_tail' l 0.

(*
 * Problem 8 [15 points, ~7 tactics for the lemma and ~4 tactics for the theorem]:
 * Try to prove sum_tail_correct directly by induction.
 * Convince yourself that you are stuck.
 *
 * Unstick yourself by stating and proving (by induction)
 * a more general helper lemma about the helper function sum_tail'.
 * Then prove sum_tail_correct in just one or two lines without induction
 * by directly applying the helper lemma.
 *
 * Hint: Unfold sum_tail and look at the proof state when you get stuck
 * proving sum_tail_correct. Why are you stuck?
 * What variable would it be helpful to abstract over to prove your goal?
 * Use these to define the helper lemma.
 *
 * Hint: In the lemma, make sure you do not introduce variables too eagerly,
 * or you may run into the same problem.
 *
 * Hint: In the proofs  (both of the helper lemma and the main theorem),
 * you will likely need a few lemmas about addition from the standard library
 * (or you can use the ring tactic).
 *)

(* your lemma here *)

Theorem sum_tail_correct :
  forall l,
    sum_tail l = sum l.
Proof.
  (* your code here *)
Admitted. (* Change to Qed *)

