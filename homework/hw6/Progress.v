(*
 * Progress
 *
 * This file contains problem 4.
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Require Import STLC.Syntax.
Require Import STLC.Subst.
Require Import STLC.Heap.
Require Import STLC.Semantics.
Require Import STLC.Types.

(*
 * In our calculus, a number of types have canonical forms: if a
 * member of that type is a value, it must have a particular form. These
 * may be useful in proving progress. 
 *)

Lemma canon_bool:
  forall env ht e,
    isValue e ->
    typed env ht e TBool ->
    exists b, e = Bool b.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_int:
  forall env ht e,
    isValue e ->
    typed env ht e TInt ->
    exists i, e = Int i.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_fun:
  forall env ht e tA tB,
    isValue e ->
    typed env ht e (tA ~> tB) ->
    exists x, exists b, e = \x, b.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

Lemma canon_ref:
  forall env ht e t,
    isValue e ->
    typed env ht e (TRef t) ->
    exists a, e = Addr a.
Proof.
  intros.
  inv H; inv H0; eauto.
Qed.

(*
 * PROBLEM 4 [30 points, ~90 tactics]: Prove progress for our calculus: 
 * given a well-typed heap, a well-typed term either can step or is a value.  
 * We've started the proof for you.
 *
 * Hint: You should familiarize yourself with the constructors of step_cbv.
 * Hint: At some point in this proof, you will destruct on can_subst from Subst.v.
 * Hint: The lemmas above about canonical forms may be useful.
 *)
Lemma progress:
  forall ht h e t,
    typed E0 ht e t ->
    heap_typed ht h ->
    (exists e' h', h; e ==> h'; e') \/ isValue e.
Proof.
  remember E0.
  induction 1; subst; intros.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 4 *)