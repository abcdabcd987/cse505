(*
 * Semantics
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Require Import STLC.Syntax.
Require Import STLC.Subst.
Require Import STLC.Heap.

Open Scope string_scope.

Notation length := List.length.

(*

Now that we have heaps, let's define our semantics!

Since we're writing a call-by-value semantics, 
we first need to define "values".

*)
Inductive isValue : expr -> Prop :=
| VLam  : forall x e, isValue (\ x, e)
| VInt  : forall i : Z, isValue i
| VBool : forall b : bool, isValue b
| VAddr : forall n, isValue (Addr n).

(*

Our step relation includes heaps as well as expressions, since heaps
can change. Look carefully over this step relation and make sure you
understand every rule!  Really, you'll need to grok this to finish the
homework.

*)
Inductive step_cbv : heap -> expr -> heap -> expr -> Prop :=
| SAppLeft :
    forall h h' e1 e1' e2,
      step_cbv h e1
               h' e1' ->
      step_cbv h (e1 @ e2)
               h' (e1' @ e2)
| SAppRight :
    forall h h' e1 e2 e2',
      isValue e1 ->
      step_cbv h e2
               h' e2' ->
      step_cbv h (e1 @ e2)
               h' (e1 @ e2')
| SApp :
    forall h x e1 e2 e1',
      isValue e2 ->
      Subst e1 e2 x e1' ->
      step_cbv h ((\ x, e1) @ e2)
               h e1'
| SRef :
    forall h h' e e',
      step_cbv h e
               h' e' ->
      step_cbv h (ref e)
               h' (ref e')
| SRefValue :
    forall h e,
      isValue e ->
      step_cbv h (ref e)
               (snoc h e) (Addr (length h))
| SDeref :
    forall h h' e e',
      step_cbv h e
               h' e' ->
      step_cbv h (! e)
               h' (! e')
| SDerefAddr :
    forall h a,
      a < length h ->
      step_cbv h (! (Addr a))
               h (lookup h a)
| SAssignLeft :
    forall h h' e1 e1' e2,
      step_cbv h e1
               h' e1' ->
      step_cbv h (e1 <- e2)
               h' (e1' <- e2)
| SAssignRight :
    forall h h' e1 e2 e2',
      isValue e1 ->
      step_cbv h e2
               h' e2' ->
      step_cbv h (e1 <- e2)
               h' (e1 <- e2')
| SAssign :
    forall h a e,
      isValue e ->
      a < length h ->
      step_cbv h (Addr a <- e)
               (replace a e h) (Bool true).

Notation "h1 ; e1 '==>' h2 ; e2" :=
  (step_cbv h1 e1 h2 e2) (at level 40, e1 at level 39, h2 at level 39).

(* any number of steps *)
Inductive star_cbv : heap -> expr -> heap -> expr -> Prop :=
| scbn_refl:
    forall h e,
      star_cbv h e h e
| scbn_step:
    forall h1 e1 h2 e2 h3 e3,
      step_cbv h1 e1 h2 e2 ->
      star_cbv h2 e2 h3 e3 ->
      star_cbv h1 e1 h3 e3.

Notation "h1 ; e1 ==>* h2 ; e2" :=
  (star_cbv h1 e1 h2 e2) (at level 40, e1 at level 39, h2 at level 39).