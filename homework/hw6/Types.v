(*
 * Types
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Require Import STLC.Syntax. (* Syntax *)
Require Import STLC.Heap. (* Heaps *)

Open Scope string_scope.

Notation length := List.length.

(* Let's talk about types! *)

(* We'll need to add a type for references to the set of types we saw lecture. *)

Inductive typ : Set :=
| TBool : typ
| TInt  : typ
| TFun  : typ -> typ -> typ
| TRef  : typ -> typ.

Notation "X ~> Y" := (TFun X Y) (at level 60).

(* An environment maps variables to types. Make sure you understand
the difference between this and a heap, which maps indices to
terms! *)

Definition env : Type :=
  string -> option typ.

(* E0 is the empty environment *)
Definition E0 : env :=
  fun _ => None.

(*

Update an environment with a new variable and type.

NOTE: Environments are different from heaps!
      We change heaps with snoc and replace.
      We change environments with extend.

*)
Definition extend (e: env) x t : env :=
  fun y =>
    if string_dec y x then
      Some t
    else
      e y.

(* In addition to our usual environments,
   we also need to type our heaps in order
   to type references. *)

(* A heap type is just a list of types. *)
Definition heap_typ :=
  list typ.

(* lookup_typ works just like lookup. *)
Definition lookup_typ (h : heap_typ) n :=
  nth n h TBool.

(* What does it mean for a term to be well-typed?
   The first 5 constructors are the same as those
   in the STLC without references.
*)

Inductive typed : env -> heap_typ -> expr -> typ -> Prop :=
| WTBool :
    forall env ht b,
      typed env ht (Bool b) TBool
| WTInt :
    forall env ht i,
      typed env ht (Int i) TInt
| WTVar :
    forall env ht x t,
      env x = Some t ->
      typed env ht (Var x) t
| WTApp :
    forall env ht e1 e2 tA tB,
      typed env ht e1 (tA ~> tB) ->
      typed env ht e2 tA ->
      typed env ht (e1 @ e2) tB
| WTLam :
    forall env ht x e tA tB,
      typed (extend env x tA) ht e tB ->
      typed env ht (\x, e) (tA ~> tB)
| WTAddr :
    forall env ht a,
      a < length ht ->
      typed env ht (Addr a) (TRef (lookup_typ ht a))
| WTRef :
    forall env ht e t,
      typed env ht e t ->
      typed env ht (ref e) (TRef t)
| WTDeref :
    forall env ht e t,
      typed env ht e (TRef t) ->
      typed env ht (! e) t
| WTAssign :
    forall env ht e1 e2 t,
      typed env ht e1 (TRef t) ->
      typed env ht e2 t ->
      typed env ht (e1 <- e2) TBool.

(* Q: What does it mean for a heap to be well-typed?

   A: The heap must be the same length as the heap type, and the term
      stored at any valid address in the heap (i.e. any address less than
      the length of the heap) should have the type it has in the heap type.
 *)

Definition heap_typed (ht : heap_typ) (h : heap) :=
  length h = length ht /\
  forall a,
    a < length h ->
    typed E0 ht (lookup h a) (lookup_typ ht a).


