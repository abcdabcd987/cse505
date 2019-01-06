(*
 * Syntax
 *)

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Frap. (* For tactics *)
Require Import STLC.StructTactics. (* For tactics *)

Open Scope string_scope.

(** syntax *)

Inductive expr : Set :=
| Bool   : bool -> expr
| Int    : Z -> expr
| Var    : string -> expr
| App    : expr -> expr -> expr
| Lam    : string -> expr -> expr
| Addr   : nat -> expr
| Ref    : expr -> expr
| Deref  : expr -> expr
| Assign : expr -> expr -> expr.

Coercion Bool : bool >-> expr.
Coercion Int  : Z >-> expr.
Coercion Var  : string >-> expr.

Notation "X @ Y"   := (App X Y)    (at level 49).
Notation "\ X , Y" := (Lam X Y)    (at level 50).
Notation "'ref' X" := (Ref X)      (at level 51).
Notation "! X"     := (Deref X)    (at level 51).
Notation "X <- Y"  := (Assign X Y) (at level 51).