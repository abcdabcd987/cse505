(* --- CSE505 HW6: Type Soundness in Call-by-value, Simply-typed Lambda Calculus with References --- *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

(**
In this homework, you'll prove soundness for a version of the
call-by-value, simply-typed lambda calculus which has been extended to
include references. You will prove this using progress and preservation.

This homework is larger than previous homeworks. The problems you must
complete are in the following files:

  Subst.v [10 points] : Problems 1 and 2 (useful lemmas)
  Heap.v [5 points] : Problem 3 (useful lemma)
  Progress.v [30 points] : Problem 4 (progress)
  Preservation.v [60 points] : Problems 5 through 9 (useful lemmas, weakening, and preservation)
  HW6.v [15 points] : Problem 10 (soundness)
  ---
  Total points: 120

This file will guide you through the proofs in order and mention
other files as relevant. It is recommended that you use this file
to guide your development, since it will help you make sense of the
structure of the different files. However, if you get stuck on one proof,
it may be helpful to skip it and move on to other proofs, then come
back to it later.

We also encourage you to start early, and to consult the lecture notes.
**)

(* --- Part 1: Syntax [0 points, 0 problems] --- *)

(*
 * Our language is the call-by-named simply-typed lambda calculus with references.
 * The syntax can be found in Syntax.v: 
 *)
Require Import STLC.Syntax.

(* That file defines expressions: *)
Print expr.

(* 
 * In addition to some standard expressions (boolean or integer values, 
 * variables, lambdas, and applications), our language contains references, 
 * which can be allocated with Ref:
 *)
Check Ref.
(* deallocated with Deref: *)
Check Deref.
(* and assigned to with Assign: *)
Check Assign.

(* 
 * At runtime, these references are stored as addresses in a heap,
 * so our syntax also contains the notion of an address Addr, although
 * the programmer never sees this:
 *)
Check Addr.

(*
 * Syntax.v also defines some useful syntax for programmers:
 *
 *   X @ Y for App X Y
 *   \ X , Y for Lam X Y
 *   ref X for Ref X
 *   ! X for Deref X
 *   X <- Y for Assign X Y
 *
 * It is worth familiarizing yourself with this syntax, since it
 * will show up throughout your later proofs.
 *)

(* --- Part 2: Substitution [10 points, 2 problems] --- *)

(*
 * In order to define our semantics, we need a notion of substitution,
 * so that when we apply a lambda:
 *
 * (\ x, e1) @ e2
 *
 * in our semantics, this will step to e2 with e1 substituted in for
 * the variable x:
 *
 * ((\ x, e1) @ e2) ==> e1 [e2 / x]
 *
 * Substitution is defined in Subst.v:
 *)
Require Import STLC.Subst.

(*
 * You should read this file in its entirety, but we will sumarize it here.
 * This file defines a relation Subst. For expressions e1, e2, and e3, 
 * and variable x, Subst e1 e2 x e3 holds when e1 [ e2 / x ] = e3. 
 *)
Print Subst.
(* It also contains a relation that holds when a variable is free: *) 
Print free.
(* and it defines closed terms, which have no free variables: *)
Print closed.

(*
 * It also defines many useful lemmas. The lemma can_subst shows
 * that we can always substitute:
 *)
Check can_subst.
(* You will need this later on in your progress proof. We will remind you later. *)

(*
 * The lemmas closed_app_intro, closed_app_inv, and so on, are facts about
 * closed terms which will be useful in several proofs:
 *)
Check closed_app_intro.
Check closed_app_inv.
(* ... and so on. *)

(*
 * This file contains two problems:
 *)

(*
 * PROBLEM 1 [5 points, ~40 tactics]: In Subst.v, fill in the proof of 
 * subst_det, which shows that our substitution relation is deterministic.
 *)
Check subst_det.

(*
 * PROBLEM 2 [5 points, ~25 tactics]: In Subst.v, fill in the proof of 
 * subst_pres_closed, which shows that closedness is preserved by substitution.
 *)
Check subst_pres_closed.

(* --- Part 3: Heaps [5 points, 1 problem] --- *)

(*
 * As we mentioned earlier, references are stored at runtime as addresses
 * on the heap. Then in order to define our semantics, we need to define heaps,
 * which are in Heap.v:
 *)
Require Import STLC.Heap.

(*
 * You should read this file, but we will summarize it here.
 * A heap is just a list of expressions:
 *)
Print heap.
(* at runtime, references are represented as addresses into this list. *)

(* Heap.v equips a heap with a lookup function: *)
Print lookup.
(* and a replace function: *)
Print replace.
(* as well as some lemmas about the replace function: *)
Check replace_nil.
Check length_replace.
(* and some lemmas relating lookup and replace: *)
Check lookup_replace_eq.
Check lookup_replace_neq.
(* These lemmas will be useful later. You will prove the second of these lemmas. *)

(*
 * PROBLEM 3 [5 points, ~8 tactics]: In Heap.v, prove lookup_replace_neq,
 * which shows that replacing a value in a heap doesn't affect lookups
 * for different values.
 *)
Check lookup_replace_neq.

(* --- Part 4 (IMPORTANT) : Semantics [0 points, 0 problems] --- *)

(*
 * Now that we have substitution and heaps, we can define the semantics
 * of our language. This is done in Semantics.v:
 *)
Require Import STLC.Semantics.

(*
 * It is very important that you familiarize with the contents of this file.
 * Your later proofs will be painful if you do not understand it. You should
 * read this file in detail, but we will summarize it here.
 *
 * Our lambda calculus is call-by-value. In contrast with the call-by-name 
 * simply-typed lambda calculus, in the call-by-value simply-typed lambda calculus, 
 * the semantics are slightly different: arguments to functions are evaluated 
 * *before* they are substituted into the function body.
 *
 * To handle this, we first need a notion of a value:
 *)
Print isValue.

(*
 * Once we have defined values, we can define our step relation,
 * step_cbv. This relation includes heaps as well as expressions, 
 * since heaps can change:
 *)
Print step_cbv.
(*
 * You should spend some time familiarizing yourself 
 * with every constructor of this relation! It will be very important
 * to understand it in order to write your proofs.
 *
 * While you should understand every rule of step_cbv, there are a few things 
 * worth paying special attention to in step_cbv:
 * 1. When a reference is allocated, the expression is stored in the heap and the 
 *    reference expression steps to the address of that expression (SRefValue).
 * 2. When a reference is deallocated, it steps to the result of looking
 *    up that reference in the current heap (SDerefAddr).
 * 3. Since our language is call-by-value as opposed to call-by-name,
 *    arguments to functions are evaluated *before* they are substituted 
 *    into the function body (SApp).
 *)

(*
 * Semantics.v also defines the transitive closure of our step relation,
 * which is standard (though it does not use the FRAP machinery):
 *)
Print star_cbv.

(*
 * The file also defines useful syntax:
 * 
 *   h1 ; e1 ==>  h2 ; e2 for step_cbv h1 e1 h2 e2  
 *   h1 ; e1 ==>* h2 ; e2 for star_cbv h1 e1 h2 e2
 *)

(*
 * Before moving on, make sure you understand this file well.
 *)

(* --- Part 5 (IMPORTANT) : Types [0 points, 0 problems] --- *)

(*
 * Our goal is to prove that our language is sound: Well-typed programs don't
 * get stuck. For references, this requires that well-typed terms don't 
 * contain pointers to unallocated addresses. We will also require that the 
 * type of the term stored at a given address never changes.
 *
 * The definition of types in our language can be found in Types.v:
 *)
Require Import STLC.Types.

(*
 * You should familiarize yourself with this file, but we will summarize
 * it here. This file defines types typ:
 *)
Print typ.
(* 
 * Most of this is standard, but we have extended it with a type 
 * TRef for references.
 *)

(*
 * In order to determine the type of an expression, we need an environment,
 * which maps variables to types (make sure you understand the difference 
 * between this and a heap, which maps indices to terms):
 *)
Print env.
(* E0 is the empty environment: *)
Print E0.
(* We can extend an environment with a new variable and type: *)
Print extend.

(*
 * In addition to our usual environments, we also need to type our heaps in order
 * to type references. A heap type is just a list of types:
 *)
Print heap_typ.
(* with a lookup function lookup_typ, which works just like lookup. *)
Print lookup_typ.

(*
 * With types and environments defined, the typed relation states
 * what it means for a term to be well-typed:
 *)
Print typed.
(*
 * You should familiarize yourself with this relation too. The first 5 constructors
 * are the same as those in the STLC without references; the last 4 constructors
 * handle references.
 *)

(*
 * Types.v also defines what it means for a heap to be well-typed:
 * The heap must be the same length as the heap type, and the term
 * stored at any valid address in the heap should have the type it 
 * has in the heap type.
 *)
Print heap_typed.

(*
 * Finally, Types.v defines some useful syntax:
 *
 *   X ~> Y for TFun X Y
 *)

(*
 * Before moving on, make sure you understand this file well.
 *)

(* --- Part 6 : Progress [30 points, 1 problem] --- *)

(* 
 * We want to prove soundness. As usual, we'll prove *progress* and
 * *preservation*. We'll start with progress, since it's easier.
 * We'll write this proof in Progress.v:
 *)
Require Import STLC.Progress.

(*
 * This file is small: Besides the progress proof you will complete, 
 * it contains some lemmas which may be useful in your progress proof.
 * These lemmas define canonical forms for certain types:
 *)
Check canon_bool.
Check canon_int.
Check canon_fun.
Check canon_ref.
(*
 * In other words, if a member of that type is a value, it must have a 
 * particular form.
 *)

(*
 * With those lemmas, you can prove progress:
 *
 * PROBLEM 4 [30 points, ~90 tactics]: In Progress.v, prove progress,
 * which states that given a well-typed heap, a well-typed term either can
 * step or is a value.
 *)

(* --- Part 7 : Preservation [60 points, 5 problems] --- *)

(*
 * Next, we'll prove preservation in Preservation.v:
 *)
Require Import STLC.Preservation.

(*
 * The hard part of proving preservation for the STLC is proving that substitution 
 * does the right thing: if it substitutes something in for a variable in a
 * body, the body had better have the same type as if we just assumed
 * that x had that type. 
 *
 * So before we can prove preservation, we're going to need to develop some 
 * machinery around environments and heap types, and then show the property
 * above. Some of that machinery is done for you, and some of it is left to you.
 *
 * You should read the file in detail, but we will summarize it.
 *)
 
(*
 * First, the file defines a notion of environments being equivalent:
 *)
Check env_equiv.
(* as well as some lemmas about this equivalence relation: *)
Check env_equiv_refl.  (* reflexivity *)
Check env_equiv_sym.   (* symmetry *)
Check env_equiv_trans. (* transitivity *)

(*
 * It also defines some lemmas about the equivalence of extended environments:
 *)
Check env_equiv_extend.
Check env_equiv_overwrite.
Check env_equiv_neq.
(* 
 * These will be useful in later proofs, so you should get to know them well.
 * There are explanations in Preservation.v.
 *)

(*
 * You will prove that equivalent environments are interchangeable:
 *
 * PROBLEM 5 [5 points, ~25 tactics]: In Preservation.v, prove env_equiv_typed,
 * which states that if a term is typed in an environment, it's typed in equivalent 
 * environments.
 *)
Check env_equiv_typed.

(*
 * Next, you will prove weakening for environments:
 *
 * PROBLEM 6 [10 points, ~70 tactics]: In Preservation.v, prove weakening,
 * which states that if a term has some type in an environment, then the term 
 * still has that type if we extend the environment with a new value for 
 * any variable that is free in the term.
 *)
Check weaken.

(*
 * Preservation.v goes on to define another notion of equivalence of environments,
 * this time with respect to free variables:
 *)
Check free_env_equiv.
(* as well as some lemmas about this equivalence relation: *)
Check free_env_equiv_refl.  (* reflexivity *)
Check free_env_equiv_sym.   (* symmetry *)
Check free_env_equiv_trans. (* transitivity *)

(*
 * It also defines some lemmas about the equivalence of extended environments,
 * which should look familiar:
 *)
Check free_env_equiv_extend.
Check free_env_equiv_overwrite.
Check free_env_equiv_neq.
(* 
 * These will be useful in later proofs, so you should get to know them well.
 * There are explanations in Preservation.v.
 *)

(*
 * This time, we handle interchangeability for you:
 *)
Check free_env_equiv_typed.

(*
 * And that takes us to proving that substitution does the right thing:
 *
 * PROBLEM 7 [10 points, ~50 tactics]: In Preservation.v, prove subst_pres_typed,
 * which states that  substitution preserves typing.
 *)
Check subst_pres_typed.

(*
 * There is one more piece of machinery: a way to extend heap types with
 * new values:
 *)
Check heap_typ_extends.
(*
 * Preservation.v explains in detail why this is necessary.
 * It also defines some useful lemmas about heap extension:
 *)
Check length_extends.
Check extends_snoc.
Check extends_refl.
(*
 * These will be useful in your preservation proof.
 *)

(*
 * Preservation.v leaves one useful fact about extend to you:
 *
 * PROBLEM 8 [5 points, ~15 tactics]: In Preservation.v, prove extends_lookup,
 * which states that if we extend a heap type with a new value, then it still
 * has all of the old values.
 *)
Check extends_lookup.

(*
 * Much like we had weakening for environments, we also need weakening for heaps.
 * Preservation.v defines heap_weakening, which states that types are preserved
 * when extending heaps:
 *)
Check heap_weakening.
(*
 * This will also be useful in your preservation proof.
 *)

(*
 * With all of that, we're ready to prove preservation:
 *
 * PROBLEM 9 [30 points, ~153 tactics]: In Preservation.v, prove preservation.
 * This looks a little different from preservation in a language without
 * references; see Preservation.v for an explanation.
 *)
Check preservation.

(* --- Part 8 : Soundness [15 points, 1 problem] --- *)

(* 
 * Having proved progress and preservation, we're finally ready to prove soundness.
 *)

(* Define the empty heap and the empty heap type *)
Definition H0 : heap := nil.
Definition HT0 : heap_typ := nil.

(* The empty heap is well-typed in the empty heap type. *)
Lemma empty_heap_typed :
  heap_typed HT0 H0.
Proof.
  split; simpl; auto.
  intros. omega.
Qed.

(* 
 * If a term is well-typed in an environment, then that environment 
 * better have definitions for all of that term's free variables. 
 *)
Lemma typed_free_env:
  forall env ht e t,
    typed env ht e t ->
    forall x,
      free e x ->
      exists tx, env x = Some tx.
Proof.
  induction 1; intros.
  - inv H.
  - inv H.
  - inv H1; eauto.
  - inv H2.
    + apply IHtyped1; auto.
    + apply IHtyped2; auto.
  - inv H1. apply IHtyped in H4.
    destruct H4 as [tx Htx].
    exists tx. unfold extend in Htx.
    break_match; congruence.
  - inv H1.
  - inv H1. auto.
  - inv H1. auto.
  - inv H2; auto.
Qed.

(* Therefore, typing in empty env implies term is closed. *)
Lemma typed_E0_closed:
  forall ht e t,
    typed E0 ht e t ->
    closed e.
Proof.
  unfold closed, not; intros.
  eapply typed_free_env in H1; eauto.
  destruct H1. discriminate.
Qed.

(* OK, soundness time! *)

(*
 * PROBLEM 10 [15 points, ~15 tactics]: Complete the proof of soundness. 
 *
 * First, prove that no term which is well-typed in an arbitrary heap
 * can get stuck. 
 *
 * Hint: This proof should use progress and preservation. 
 *)
Lemma soundness' : (* ~10 tactics *)
  forall h e t h' e',
    (h; e ==>* h'; e') ->
    forall ht,
      typed E0 ht e t ->
      heap_typed ht h ->
      (exists e'' h'', h'; e' ==> h''; e'') \/ isValue e'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* 
 * Now, prove that terms which are well-typed in the empty heap 
 * don't get stuck. 
 *)
Lemma soundness : (* ~5 tactics *)
  forall e t h' e',
    typed E0 HT0 e t ->
    (H0; e ==>* h'; e') ->
    (exists e'' h'', h'; e' ==> h''; e'') \/ isValue e'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)
(* END PROBLEM 10 *)
