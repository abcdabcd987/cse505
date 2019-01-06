Require Import List.
Require Import String.
Require Import ZArith.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Require Import Imp.StructTactics.
Require Import Imp.ImpSyntax.
Require Import Imp.ImpCommon.
Require Import Imp.ImpEval.

(** misc *)

Lemma locate_inv :
  forall env x name params body ret,
    locate env x = Some (Func name params body ret) ->
    x = name.
Proof.
  induction env; simpl; intros.
  - congruence.
  - repeat break_match; subst.
    + congruence.
    + find_apply_hyp_hyp; auto.
Qed.

(** eval facts *)

Lemma eval_unop_det :
  forall op v v1 v2,
    eval_unop op v v1 ->
    eval_unop op v v2 ->
    v1 = v2.
Proof.
  intros.
  repeat on (eval_unop _ _ _), invc; auto.
Qed.

Lemma eval_binop_det :
  forall op vL vR v1 v2,
    eval_binop op vL vR v1 ->
    eval_binop op vL vR v2 ->
    v1 = v2.
Proof.
  intros.
  repeat on (eval_binop _ _ _ _), invc; auto.
Qed.

Lemma eval_e_det :
  forall s h e v1 v2,
    eval_e s h e v1 ->
    eval_e s h e v2 ->
    v1 = v2.
Proof.
  intros. prep_induction H.
  induction H; intros;
    on (eval_e _ _ _ _), invc;
    repeat find_apply_hyp_hyp;
    subst; try congruence.
  - find_eapply_lem_hyp eval_unop_det; eauto.
  - find_eapply_lem_hyp eval_binop_det; eauto.
Qed.

Lemma eval_e_len_a_inv :
  forall s h e x a l,
    eval_e s h (Elen e) x ->
    eval_e s h e (Vaddr a) ->
    read h a = Some (Vint l) ->
    x = Vint l.
Proof.
  intros.
  invc H.
  - eapply ImpSemanticsFacts.eval_e_det in H0; eauto. congruence.
  - eapply ImpSemanticsFacts.eval_e_det in H0; eauto. congruence.
Qed.

Lemma eval_e_idx_a_inv :
  forall s h e1 e2 x a i l,
    eval_e s h (Eidx e1 e2) x ->
    eval_e s h e1 (Vaddr a) ->
    eval_e s h e2 (Vint i) ->
    read h a = Some (Vint l) ->
    read h (Z.succ (a + i)) = Some x.
Proof.
  intros.
  invc H.
  - eapply ImpSemanticsFacts.eval_e_det in H0; eauto.
    eapply ImpSemanticsFacts.eval_e_det in H1; eauto.
    congruence.
  - eapply ImpSemanticsFacts.eval_e_det in H0; eauto.
    congruence.
Qed.
