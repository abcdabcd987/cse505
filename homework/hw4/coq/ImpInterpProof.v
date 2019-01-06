Require Import List.
Require Import String.
Require Import ZArith.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Require Import Frap.

Require Import Imp.StructTactics.
Require Import Imp.ImpSyntax.
Require Import Imp.ImpCommon.
Require Import Imp.ImpEval.
Require Import Imp.ImpSemanticsFacts.
Require Import Imp.ImpInterp.

(*
 * In this file, you will prove a correspondence between your interpreter and
 * your semantics.
 *
 * Some of the lemmas from ImpCommon.v and ImpSemanticsFacts.v will be useful
 * in these proofs, so you should make sure you are familiar with the lemmas
 * in those files.
 *
 * We have also included some useful tactics to help you with your proofs.
 * For example, while we could prove that unary operators behave as 
 * expected this way (this is purposely extremely manual so you can step through it):
 *)
Lemma interp_op1_eval_op1' :
  forall op v v',
    interp_op1 op v = Some v' ->
    eval_unop op v v'.
Proof.
  unfold interp_op1. intros.
  destruct op.
  - destruct v.
    + discriminate.
    + inversion H. constructor.
    + discriminate.
    + discriminate.
  - destruct v.
    + inversion H. constructor.
    + discriminate.
    + discriminate.
    + discriminate. 
Qed.
(*
 * We can use the break_match tactic to automatically destruct on both
 * op and v, and then use Coq's tacticals (repeat, try, and the semicolon)
 * to make the proof very concise:
 *)
Lemma interp_op1_eval_op1 :
  forall op v v',
    interp_op1 op v = Some v' ->
    eval_unop op v v'.
Proof.
  unfold interp_op1; intros.
  repeat break_match; subst; try discriminate; inversion H; constructor.
Qed.
(*
 * You will almost certainly want to use the break_match tactic to simplify
 * your proofs in this section.
 *)

Lemma eval_op1_interp_op1 :
  forall op v v',
    eval_unop op v v' ->
    interp_op1 op v = Some v'.
Proof.
  inversion 1; auto.
Qed.

(*
 * Problem 3 [15 points, ~10 tactics]: Complete this proof.
 *
 * Hint: Read about the break_match tactic and Coq's tacticals above
 * before writing this proof.
 *)
Lemma interp_op2_eval_op2 :
  forall op v1 v2 v',
    interp_op2 op v1 v2 = Some v' ->
    eval_binop op v1 v2 v'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * Problem 1 continued (correctness test) [necessary to get points for Problem 1]: 
 * Uncomment this proof. This proof should go through once you have completed 
 * the problems in ImpInterp.v. If it does not, fix your interp_op2 code.
 *)
Lemma eval_op2_interp_op2 :
  forall op v1 v2 v',
    eval_binop op v1 v2 v' ->
    interp_op2 op v1 v2 = Some v'.
Proof.
  (* inversion 1; auto.
  - simpl. break_match; [congruence | auto].
  - simpl. break_match; [congruence | auto].*) (* UNCOMMENT *)
Admitted. (* CHANGE TO QED *)

Lemma interp_e_eval_e :
  forall s h e v,
    interp_e s h e = Some v ->
    eval_e s h e v.
Proof.
  induction e; simpl; intros.
  - inv H; ee.
  - ee.
  - repeat break_match; try discriminate.
    ee. apply interp_op1_eval_op1; auto.
  - repeat break_match; try discriminate.
    ee. apply interp_op2_eval_op2; auto.
  - repeat break_match; try discriminate.
    + find_inversion. eapply eval_len_s; eauto.
    + find_inversion. eapply eval_len_a; eauto.
  - repeat break_match; try discriminate.
    + find_inversion. eapply eval_idx_s; eauto.
    + eapply eval_idx_a; eauto.
Qed.

Lemma eval_e_interp_e :
  forall s h e v,
    eval_e s h e v ->
    interp_e s h e = Some v.
Proof.
  induction 1; simpl; auto.
  - repeat break_match; try discriminate.
    find_inversion. apply eval_op1_interp_op1; auto.
  - repeat break_match; try discriminate.
    repeat find_inversion. apply eval_op2_interp_op2; auto.
  - break_match; try discriminate. find_inversion.
    break_match; try discriminate. find_inversion.
    reflexivity.
  - break_match; try discriminate.
    find_inversion. reflexivity.
  - break_match; try discriminate.
    find_inversion. repeat find_rewrite.
    do 2 (break_match; try omega). auto.
  - break_match; try discriminate. find_inversion.
    break_match; try discriminate. find_inversion.
    break_match; try omega.
    break_match; try discriminate.
    find_inversion; auto.
Qed.

Lemma interps_e_evals_e :
  forall s h es vs,
    interps_e s h es = Some vs ->
    evals_e s h es vs.
Proof.
  induction es; simpl; intros.
  - find_inversion. ee.
  - repeat break_match; try discriminate.
    find_inversion. ee.
    apply interp_e_eval_e; auto.
Qed.

Lemma evals_e_interps_e :
  forall s h es vs,
    evals_e s h es vs ->
    interps_e s h es = Some vs.
Proof.
  induction 1; simpl; intros; auto.
  find_apply_lem_hyp eval_e_interp_e.
  repeat find_rewrite. auto.
Qed.

(*
 * Problem 4 [40 points, <100 tactics]: Prove interp_s_eval_s.
 *
 * Hint: You will likely want the break_match tactic again.
 * You should also familiarize yourself with the lemmas in ImpCommon.v and
 * ImpSemanticsFacts.v before writing this proof, and consider using them
 * if you get stuck.
 *)
Lemma interp_s_eval_s :
  forall fuel env s h p s' h',
    interp_s fuel env s h p = Some (s', h') ->
    eval_s env s h p s' h'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

Lemma interp_p_eval_p :
  forall n funcs main ret h' v',
    interp_p n (Prog funcs main ret) = Some (h', v') ->
    eval_p (Prog funcs main ret) h' v'.
Proof.
  unfold interp_p; intros.
  repeat break_match; try discriminate.
  repeat find_inversion.
  find_apply_lem_hyp interp_s_eval_s.
  find_apply_lem_hyp interp_e_eval_e.
  ee.
Qed.
