(*
 * Preservation
 *
 * This file contains problems 5 through 9.
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

Open Scope string_scope.

Notation length := List.length.

(*

Our proof of preservation is going to be a little harder than our progress proof;
we're going to need to develop some machinery around environments and
heap types.

*)

(* Equivalence of environments *)
Definition env_equiv (e1 e2: env) : Prop :=
  forall s, e1 s = e2 s.

(* Some lemmas about this equivalence relation. *)

(* reflexivity *)
Lemma env_equiv_refl:
  forall env,
    env_equiv env env.
Proof.
  unfold env_equiv; auto.
Qed.

(* symmetry *)
Lemma env_equiv_sym:
  forall e1 e2,
    env_equiv e1 e2 ->
    env_equiv e2 e1.
Proof.
  unfold env_equiv; auto.
Qed.

(* transitivity *)
Lemma env_equiv_trans:
  forall e1 e2 e3,
    env_equiv e1 e2 ->
    env_equiv e2 e3 ->
    env_equiv e1 e3.
Proof.
  unfold env_equiv; intros.
  congruence.
Qed.

(* extending environments with the same value preserves equivalence *)
Lemma env_equiv_extend:
  forall env1 env2 x t,
    env_equiv env1 env2 ->
    env_equiv (extend env1 x t) (extend env2 x t).
Proof.
  unfold env_equiv, extend; intros.
  break_match; auto.
Qed.

(* if we extend twice with the same variable, it's equivalent to just
extending with the second value (i.e. we "overwrite" values *)
Lemma env_equiv_overwrite:
  forall env x t1 t2,
    env_equiv (extend (extend env x t1) x t2)
              (extend env x t2).
Proof.
  unfold env_equiv, extend; intros.
  break_match; auto.
Qed.

(* If we extend twice with different variables,
   both possible orders result in equivalent envs.
*)
Lemma env_equiv_neq:
  forall env1 env2 x1 t1 x2 t2,
    x1 <> x2 ->
    env_equiv env1 env2 ->
    env_equiv (extend (extend env1 x1 t1) x2 t2)
              (extend (extend env2 x2 t2) x1 t1).
Proof.
  unfold env_equiv, extend; intros.
  break_match; break_match; congruence.
Qed.

(*
 * PROBLEM 5 [5 points, ~25 tactics]: Prove that if a term is typed in an 
 * environment, it's typed in equivalent environments.
 *
 * Hint: The lemmas above about env_equiv may be useful.
 *)
Lemma env_equiv_typed:
  forall env1 ht e t,
    typed env1 ht e t ->
    forall env2,
      env_equiv env1 env2 ->
      typed env2 ht e t.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 5 *)

(*

Weakening is a structural property of environments: it means that if a
term has some type in an environment, then the term still has that
type if we extend the environment with a new value for any variable
that is free in the term. It's called "weakening" because we can prove
that a term has a type in one environment by removing bindings from
another environment where we know the term is typable.

*)

(*
 * PROBLEM 6 [10 points, ~70 tactics]: Prove weakening for environments.
 *
 * Hint: The lemmas above about env_equiv, including the lemma you just proved,
 * may be useful.
 *)
Lemma weaken:
  forall env ht e t,
    typed env ht e t ->
    forall x t',
      ~ free e x ->
      typed (extend env x t') ht e t.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 6 *)

(* Next, we'll define another notion of equivalence: equivalence of
environments with respect to the free variables in a particular
term. If two environments have the same value for every free variable
in a term, then those environments should be interchangeable when
typing that term. *)

Definition free_env_equiv (E: expr) (e1 e2: env) : Prop :=
  forall x,
    free E x ->
    e1 x = e2 x.

(* We'll prove all the same thigs about this equivalence relation *)
Lemma free_env_equiv_refl:
  forall E env,
    free_env_equiv E env env.
Proof.
  unfold free_env_equiv; auto.
Qed.

Lemma free_env_equiv_sym:
  forall E e1 e2,
    free_env_equiv E e1 e2 ->
    free_env_equiv E e2 e1.
Proof.
  unfold free_env_equiv; intros.
  symmetry. apply H; auto.
Qed.

Lemma free_env_equiv_trans:
  forall E e1 e2 e3,
    free_env_equiv E e1 e2 ->
    free_env_equiv E e2 e3 ->
    free_env_equiv E e1 e3.
Proof.
  unfold free_env_equiv; intros.
  apply eq_trans with (y := e2 x); auto.
Qed.

Lemma free_env_equiv_extend:
  forall E env1 env2 x t,
    free_env_equiv E env1 env2 ->
    free_env_equiv E (extend env1 x t) (extend env2 x t).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; auto.
Qed.

Lemma free_env_equiv_overwrite:
  forall E env x t1 t2,
    free_env_equiv E (extend (extend env x t1) x t2)
                     (extend env x t2).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; auto.
Qed.

Lemma free_env_equiv_neq:
  forall E env1 env2 x1 t1 x2 t2,
    x1 <> x2 ->
    free_env_equiv E env1 env2 ->
    free_env_equiv E (extend (extend env1 x1 t1) x2 t2)
                     (extend (extend env2 x2 t2) x1 t1).
Proof.
  unfold free_env_equiv, extend; intros.
  break_match; break_match; subst; auto.
  congruence.
Qed.

(* Here's where we prove interchangeability *)
Lemma free_env_equiv_typed:
  forall env1 ht e t,
    typed env1 ht e t ->
    forall env2,
      free_env_equiv e env1 env2 ->
      typed env2 ht e t.
Proof.
  unfold free_env_equiv.
  induction 1; intros.
  - constructor.
  - constructor.
  - constructor. symmetry.
    rewrite <- H. apply H0.
    constructor.
  - econstructor; eauto.
    + apply IHtyped1; intuition.
      apply H1; apply FreeApp_l; auto.
    + apply IHtyped2; intuition.
      apply H1; apply FreeApp_r; auto.
  - econstructor; eauto.
    apply IHtyped; auto.
    unfold extend; intros.
    break_match; auto.
    apply H0. constructor; auto.
  - constructor. auto.
  - constructor. apply IHtyped.
    intros.
    apply H0. constructor. auto.
  - constructor. apply IHtyped.
    intros.
    apply H0. constructor. auto.
  - econstructor.
    + apply IHtyped1. intros.
      apply H1. constructor. auto.
    + apply IHtyped2. intros.
      apply H1. apply FreeAssign_r. auto.
Qed.

(* OK, here's the lemma we needed all that for. The hard part of
proving preservation for the STLC is proving that substitution does
the right thing: if it substitutes something in for a variable in a
body, the body had better have the same type as if we just assumed
that x had that type. *)

(*
 * PROBLEM 7 [10 points, ~50 tactics]: Prove that substitution preserves typing.
 *
 * Hint: The lemmas above about env_equiv and free_env_equiv may be useful,
 * as may be weakening.
 *)
Lemma subst_pres_typed:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    closed e2 ->
    forall env ht tA tB,
      typed (extend env x tA) ht e1 tB ->
      typed env ht e2 tA ->
      typed env ht e3 tB.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 7 *)

(** We're almost there. The last thing we'll need to do is to provide
a way to extend heap types with new values during our preservation
proof. To see why, let's take a look at a version of preservation that
looks a lot like the one for STLC without references: *)

Lemma wrong_preservation:
  forall h h' e e',
    h; e ==> h'; e' ->
    closed e ->
    forall ht t,
      heap_typed ht h ->
      typed E0 ht e t ->
      typed E0 ht e' t.
Abort.

(* The problem is that we're stuck with the same heap type. This is an
issue because when we allocate a new reference, we'll need to extend
our heap type with a type for the new reference cell. So let's
establish what it means for one heap to extend another: *)

Inductive heap_typ_extends: heap_typ -> heap_typ -> Prop :=
| heap_typ_extends_nil :
    forall h, heap_typ_extends h nil
| heap_typ_extends_cons :
    forall h h' x,
      heap_typ_extends h' h ->
      heap_typ_extends (x :: h') (x :: h).

(* We'll need some facts about this definition of heap extension. *)

(* If an address was in our heap type and we extend the heap, we don't
   affect the type for that address.
*)

(*
 * PROBLEM 8 [5 points, ~15 tactics]: Prove extends_lookup.
 *)
Lemma extends_lookup :
  forall h h' a,
    a < length h ->
    heap_typ_extends h' h ->
    lookup_typ h' a = lookup_typ h a.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 8 *)

(* Extending a heap increases its length *)
Lemma length_extends :
  forall h h',
    heap_typ_extends h' h ->
    forall a,
      a < length h ->
      a < length h'.
Proof.
  induction 1; intros; simpl in *.
  - omega.
  - destruct a.
    + omega.
    + apply lt_n_S. intuition.
Qed.

(* If we snoc a value onto a heap, that extends the heap. *)
Lemma extends_snoc :
  forall h x,
    heap_typ_extends (snoc h x) h.
Proof.
  intros.
  induction h; simpl in *;
  constructor; auto.
Qed.

(* Heaps extend themselves *)
Lemma extends_refl :
  forall h,
    heap_typ_extends h h.
Proof.
  induction h; constructor; auto.
Qed.

(* We'll need anonther version of weakening:
   types are preserved when extending heaps.
*)
Lemma heap_weakening :
  forall env ht ht' e t,
    typed env ht e t ->
    heap_typ_extends ht' ht ->
    typed env ht' e t.
Proof.
  induction 1; intros; simpl; try solve [econstructor; eauto].
  erewrite <- extends_lookup; eauto.
  constructor.
  eapply length_extends; eauto.
Qed.

(*

OK, we're ready to prove preservation. Note our new theorem
statement: Instead of saying that the term we step to is well-typed
with our starting heap type, we're now saying that there is *some*
heap type which is an extension of our heap type under which the new
term is well-typed. In practice, this new heap type will always either
be the same or the same plus a single type (when a new ref cell is
allocated).

*)

(*
 * PROBLEM 9 [30 points, ~153 tactics]: Prove preservation.
 *
 * Hint: You'll need to be careful about when to provide a witness for the 
 * existential, and "eexists" is your friend.
 * Hint: You will need many lemmas from above, as well as from other files.
 * You should familiarize yourself with all of these lemmas.
 *)
Lemma preservation:
  forall h h' e e',
    h; e ==> h'; e' ->
    closed e ->
    forall ht t,
      heap_typed ht h ->
      typed E0 ht e t ->
      exists ht',
        heap_typ_extends ht' ht /\
        typed E0 ht' e' t /\
        heap_typed ht' h'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 9 *)