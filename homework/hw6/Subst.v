(*
 * Substitution and free variables
 *
 * This file contains problems 1 and 2.
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Open Scope string_scope.

Notation length := List.length.

Require Import STLC.Syntax.

(* --- Substitution --- *)

(** e1 [ e2 / x ] = e3 *)
Inductive Subst : expr -> expr -> string ->
                  expr -> Prop :=
| SubstBool:
    forall b e x,
      Subst (Bool b) e x
            (Bool b)
| SubstInt:
    forall i e x,
      Subst (Int i) e x
            (Int i)
| SubstVar_same:
    forall e x,
      Subst (Var x) e x
            e
| SubstVar_diff:
    forall e x1 x2,
      x1 <> x2 ->
      Subst (Var x1) e x2
            (Var x1)
| SubstApp:
    forall e1 e2 e x e1' e2',
      Subst e1 e x e1' ->
      Subst e2 e x e2' ->
      Subst (App e1 e2) e x
            (App e1' e2')
| SubstLam_same:
    forall e1 x e,
      Subst (Lam x e1) e x
            (Lam x e1)
| SubstLam_diff:
    forall e1 x1 x2 e e1',
      x1 <> x2 ->
      Subst e1 e x2 e1' ->
      Subst (Lam x1 e1) e x2
            (Lam x1 e1')
| SubstAddr :
    forall a e x,
      Subst (Addr a) e x
            (Addr a)
| SubstRef :
    forall r e x r',
      Subst r e x r' ->
      Subst (Ref r) e x (Ref r')
| SubstDeref :
    forall r e x r',
      Subst r e x r' ->
      Subst (Deref r) e x (Deref r')
| SubstAssign:
    forall e1 e2 e x e1' e2',
      Subst e1 e x e1' ->
      Subst e2 e x e2' ->
      Subst (Assign e1 e2) e x
            (Assign e1' e2').

(* We can always substitute. You'll destruct the value of can_subst on
particular arguments somewhere in the progress proof. *)
Lemma can_subst:
  forall e1 e2 x,
    exists e3, Subst e1 e2 x e3.
Proof.
  induction e1; intros.
  - econstructor; constructor.
  - econstructor; constructor.
  - case (string_dec x s); intros.
    + subst. econstructor; constructor.
    + econstructor; constructor; auto.
  - edestruct IHe1_1; edestruct IHe1_2.
    econstructor; econstructor; eauto.
  - edestruct IHe1.
    case (string_dec x s); intros.
    + subst. econstructor; constructor.
    + econstructor; constructor; eauto.
  - eexists; econstructor.
  - edestruct IHe1; eexists; constructor; eauto.
  - edestruct IHe1; eexists; constructor; eauto.
  - edestruct IHe1_1; edestruct IHe1_2.
    eexists; constructor; eauto.
Qed.

(*
 * PROBLEM 1 [5 points, ~40 tactics]: Prove that our substitution relation 
 * is deterministic.
 *
 * Hint: You may find that the equality or f_equal tactic is useful in this proof.
 *)
Lemma subst_det:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    forall e3',
      Subst e1 e2 x e3' ->
      e3 = e3'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 1 *)

(** What does it mean for a variable to be free in an expression?
    There shouldn't be any surprises here, since references don't 
    affect whether a variable is bound or not.
 *)
Inductive free : expr -> string -> Prop :=
| FreeVar:
    forall x,
      free (Var x) x
| FreeApp_l:
    forall x e1 e2,
      free e1 x ->
      free (App e1 e2) x
| FreeApp_r:
    forall x e1 e2,
      free e2 x ->
      free (App e1 e2) x
| FreeLam:
    forall x1 x2 e,
      free e x1 ->
      x1 <> x2 ->
      free (Lam x2 e) x1
| FreeRef :
    forall x r,
      free r x ->
      free (Ref r) x
| FreeDeref :
    forall x r,
      free r x ->
      free (Deref r) x
| FreeAssign_l:
    forall x e1 e2,
      free e1 x ->
      free (Assign e1 e2) x
| FreeAssign_r:
    forall x e1 e2,
      free e2 x ->
      free (Assign e1 e2) x.

(* If a variable isn't free in an expression, 
   substituting that variable doesn't change the expression. *)

Lemma subst_only_free:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    ~ free e1 x ->
    e1 = e3.
Proof.
  induction 1; intros; auto.
  - destruct H. constructor.
  - f_equal.
    + apply IHSubst1; intuition.
      apply H1; apply FreeApp_l; auto.
    + apply IHSubst2; intuition.
      apply H1; apply FreeApp_r; auto.
  - rewrite IHSubst; auto.
    intuition. apply H1.
    constructor; auto.
  - rewrite IHSubst; auto.
    intuition. apply H0.
    constructor; auto.
  - rewrite IHSubst; auto.
    intuition. apply H0.
    constructor; auto.
  - f_equal.
    + apply IHSubst1; intuition.
      apply H1; apply FreeAssign_l; auto.
    + apply IHSubst2; intuition.
      apply H1; apply FreeAssign_r; auto.
Qed.

(** Closed terms have no free variables *)
Definition closed (e: expr) : Prop :=
  forall x, ~ free e x.

(* These are a bunch of facts about closed terms. 
   We've completed the proofs, but look over them because 
   they are will be useful later.
 *)
Lemma closed_app_intro:
  forall e1 e2,
    closed e1 ->
    closed e2 ->
    closed (e1 @ e2).
Proof.
  unfold closed, not; intros.
  inv H1.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma closed_app_inv:
  forall e1 e2,
    closed (e1 @ e2) ->
    closed e1 /\ closed e2.
Proof.
  unfold closed, not; split; intros.
  - eapply H; eauto.
    apply FreeApp_l; eauto.
  - eapply H; eauto.
    apply FreeApp_r; eauto.
Qed.

Lemma closed_lam_intro:
  forall x e,
    (forall y, y <> x -> ~ free e y) ->
    closed (\x, e).
Proof.
  unfold closed, not; intros.
  inv H0. eapply H; eauto.
Qed.

Lemma closed_lam_inv:
  forall x e,
    closed (\x, e) ->
    (forall y, y <> x -> ~ free e y).
Proof.
  unfold closed, not; intros.
  cut (free (\x, e) y); intros.
  - eapply H; eauto.
  - constructor; auto.
Qed.

Lemma closed_ref_intro:
  forall e,
    closed e ->
    closed (ref e).
Proof.
  unfold closed, not; intros.
  inv H0. eauto.
Qed.

Lemma closed_ref_inv:
  forall e,
    closed (ref e) ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply H. 
  constructor. eauto.
Qed.

Lemma closed_deref_intro:
  forall e,
    closed e ->
    closed (! e).
Proof.
  unfold closed, not; intros.
  inv H0. eauto.
Qed.

Lemma closed_deref_inv:
  forall e,
    closed (! e) ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply H. 
  constructor. eauto.
Qed.

Lemma closed_assign_intro:
  forall e1 e2,
    closed e1 ->
    closed e2 ->
    closed (e1 <- e2).
Proof.
  unfold closed, not; intros.
  inv H1.
  - eapply H; eauto.
  - eapply H0; eauto.
Qed.

Lemma closed_assign_inv:
  forall e1 e2,
    closed (e1 <- e2) ->
    closed e1 /\ closed e2.
Proof.
  unfold closed, not; split; intros.
  - eapply H; eauto.
    apply FreeAssign_l; eauto.
  - eapply H; eauto.
    apply FreeAssign_r; eauto.
Qed.

(*
 * PROBLEM 2 [5 points, ~25 tactics]: Prove that closedness is preserved 
 * by substitution.
 *
 * Hint: This proof should use many of the lemmas defined above.
 *)
Lemma subst_pres_closed:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 ->
    closed e1 ->
    closed e2 ->
    closed e3.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 2 *)
