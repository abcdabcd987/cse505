(** * CSE505 - HW2 *)

Require Import Frap.

(*
 * This homework is loosely based on a problem set from the MIT FRAP course,
 * but rewritten for CSE505.
 *)

(*
 * In this assignment, we will work with a simple language of string programs.
 * The [Prog] datatype defines abstract syntax trees for this language.
 *)

Inductive Prog :=
  | Const (s : string) (* constant string *)
  | Add (p1 p2 : Prog) (* concatenate p1 and p2 *)
  | Mul (p : Prog) (n : nat) (* repeat p n times *)
  | Rev (p : Prog) (* reverse p *)
  .

(* Your job is to define a module implementing the following
 * signature.  We ask you to implement a file HW2.v, where the skeleton is
 * already given, such that it can be checked against this signature by
 * successfully processing a third file (HW2Check.v) with a command like so:
 * <<
    Require HW2Sig HW2.

    Module M : HW2Sig.S := HW2.
   >>
 * You'll need to build your module first, which the default target of our
 * handy Makefile does for you automatically.  Note that the _CoqProject
 * file included here is also important for making compilation and
 * interactive editing work.  Your Hw2.v file is what you upload to the course
 * web site to get credit for doing the assignment.
 *)

(* Finally, here's the actual signature to implement. *)
Module Type S.

  (* --- Part 1 --- *)

  (* Problem 1 [10 points]: Implement the `repeat` function, which repeats a string
   n times. If n is 0, this should return the empty string.
   For example, repeat "foo" 3 = "foofoofoo". *)
   Parameter repeat : string -> nat -> string.

   Axiom repeatTest1 : repeat "foo" 3 = "foofoofoo".
   Axiom repeatTest2 : forall s, repeat s 0 = "".
   Axiom repeatTest3 : repeat "bar" 1 = "bar".

  (* Problem 2 [10 points]: Write a function `reverse` that reverses a string.
   *)
   Parameter reverse : string -> string.

   Axiom revTest1 : reverse "cse505" = "505esc".
   Axiom revTest2 : reverse "" = "".

  (* Problem 3 [15 points]: Define [run] such that [run p] computes the string that
   * running the program [p] should result in. See the comments in the definition of
   * Prog as well as the examples below for details.
   *)
   Parameter run : Prog -> string.

   Axiom run_Example1 : run (Const "foo") = "foo".
   Axiom run_Example2 : run (Add (Const "1") (Const "2")) = "12".
   Axiom run_Example3 : run (Rev (Mul (Const "12") 3)) = "212121".

  (* Problem 4 [10 points]: Prove that the length of the result of appending
   * two strings is the same as the sum of the lengths of each string.
   *)
   Axiom len_app_plus :
     forall s1 s2,
       String.length (s1 ++ s2) = String.length s1 + String.length s2.

   (* Problem 5 [10 points]: Prove that the length of repeating a string n times
    * is n times the length of the string.
    *)
   Axiom len_repeat:
     forall s n,
       String.length (repeat s n) = n * String.length s.

   (* Problem 6 [10 points]: Prove that the length of reversing a string is the
    * same as the length of the string.
    *)
   Axiom len_rev:
     forall s,
       String.length (reverse s) = String.length s.

   (* The sum of the lengths of subexpressions *)
   Parameter sub_len : Prog -> nat.

  (* Problem 7 [20 points]: Show that running a program preserves the
   * length of the subexpressions.
   *)
   Axiom run_pres_len:
     forall p,
       String.length (run p) = sub_len p.

   (* --- Part 2: From http://homes.cs.washington.edu/~jrw12/InductionExercises.html --- *)

   (* add a list of natural numbers *)
   Parameter sum : list nat -> nat.

   (* tail-recursive version of sum *)
   Parameter sum_tail : list nat -> nat.

   (*
    * Problem 8 [15 points]:
    * Try to prove sum_tail_correct directly by induction.
    * Convince yourself that you are stuck.
    *
    * Unstick yourself by stating and proving (by induction)
    * a more general helper lemma about the helper function sum_tail'.
    * Then prove sum_tail_correct in just one or two lines without induction
    * by directly applying the helper lemma.
    *)
    Axiom sum_tail_correct :
      forall l,
        sum_tail l = sum l.
End S.
