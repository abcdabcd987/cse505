(*
 * Heaps
 *
 * This file contains problem 3.
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Require Import STLC.Syntax.

Open Scope string_scope.

Notation length := List.length.

(*

Here we define "heaps", which our references will index into.

A heap is just a list of expressions (in our uses later below,
they will always be values) which can be indexed into.

*)

Definition heap := list expr.

(*

We define lookup in terms of the "nth" function:
  https://coq.inria.fr/library/Coq.Lists.List.html

nth takes a default argument (consider why!), but
we will not actually end up in the default case
in our code later below.

*)

Definition lookup (h : heap) n :=
  nth n h true.

(* snoc is cons, backwards. It adds an element to the end of a list. *)
Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
  match l with
    | nil => x :: nil
    | h :: t => h :: snoc t x
  end.

(** We will need some boring lemmas about [snoc]. We've completed the
proofs for you, but look over them since you'll need them later.  *)

Lemma length_snoc : forall A (l:list A) n,
  length (snoc l n) = S (length l).
Proof.
  induction l; intros; auto.
  simpl. rewrite IHl. auto.
Qed.

Lemma nth_lt_snoc : forall A (l:list A) x d n,
  n < length l ->
  nth n l d = nth n (snoc l x) d.
Proof.
  induction l; intros; simpl in *.
  - omega.
  - break_match; auto.
    apply IHl. omega.
Qed.

Lemma nth_eq_snoc : forall A (l:list A) x d,
  nth (length l) (snoc l x) d = x.
Proof.
  induction l; intros; auto.
  simpl. rewrite IHl. auto.
Qed.

(** To update the heap, we use the [replace] function, which replaces
    the contents of a cell at a particular index. *)

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t => 
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(** Of course, we also need some boring lemmas about [replace], which
    are also fairly straightforward to prove. *)

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A (l:list A) n x,
  length (replace n x l) = length l.
Proof.
  induction l; intros; simpl;
  destruct n; simpl; eauto.
Qed.

Lemma lookup_replace_eq : forall h a t,
  a < length h -> 
  lookup (replace a t h) a = t.
Proof.
  unfold lookup.
  induction h; intros; simpl in *; auto.
  - omega.
  - destruct a0; simpl; auto.
    apply IHh. omega.
Qed.

(*
 * PROBLEM 3 [5 points, ~8 tactics]: Prove that replacing a value in a heap doesn't 
 * affect lookups for different values. We have started this proof for you.
 *)
Lemma lookup_replace_neq : forall a1 a2 t h,
  a1 <> a2 ->
  lookup (replace a1 t h) a2 = lookup h a2.
Proof.
  unfold lookup. induct a1; intros.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
