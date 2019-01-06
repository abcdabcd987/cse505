(** * CSE505 HW3: ADTs *)

Require Import Frap.

(*
 * In this homework, we will implement a map ADT using association lists,
 * and prove that the implementation satisfies the specification.
 * It may help to look at the DataAbstraction.v file in FRAP to get more familiar
 * with the Coq module system.
 *
 * In order to implement maps, we must have keys with a boolean
 * equality function. We start by defining the type of these keys.
 * This definition comes from the FRAP code in DataAbstraction.v.
 *)
Module Type SET_WITH_EQUALITY.
  Parameter t : Set.
  Parameter equal : t -> t -> bool.

  Axiom equal_ok : forall a b, if equal a b then a = b else a <> b.
End SET_WITH_EQUALITY.

(*
 * One example of a type with a boolean equality function
 * is the natural numbers. This implementation also comes from the
 * FRAP code in DataAbstraction.v.
 *)
Module NatWithEquality <: SET_WITH_EQUALITY with Definition t := nat.
  Definition t := nat.

  Fixpoint equal (a b : nat) : bool :=
    match a, b with
    | 0, 0 => true
    | S a', S b' => equal a' b'
    | _, _ => false
    end.

  Theorem equal_ok : forall a b, if equal a b then a = b else a <> b.
  Proof.
    induct a; simplify.

    cases b.
    equality.
    equality.

    cases b.
    equality.
    specialize (IHa b).
    cases (equal a b).
    equality.
    equality.
  Qed.
End NatWithEquality.

(*
 * With these definitions, we can now define our map ADT.
 * This is not too different from the map interface in OCaml:
 * http://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.Make.html
 *)
Module Type MAP (s : SET_WITH_EQUALITY).
  Definition key := s.t. (* The type of keys *)
  Parameter t : Set -> Set. (* A collection type that holds values *)
  Parameter empty : forall {val : Set}, t val. (* The empty map *)

  (* --- Basic operations --- *)

  (*
   * Find the value v that a key maps to, returning Some v if the
   * key is in the map, and None otherwise.
   *)
  Parameter find : forall {val : Set}, key -> t val -> option val.

  (*
   * Add a key and value to the map, and return the updated map.
   *)
  Parameter add : forall {val : Set}, key -> val -> t val -> t val.

  (*
   * Remove the value that the key maps to from the map.
   *)
  Parameter remove : forall {val : Set}, key -> t val -> t val.

  (* --- Specifications for basic operations --- *)

  (*
   * Find of any element in the empty map is None
   *)
  Axiom find_empty :
    forall {val : Set} k,
      @find val k empty = None.

  (*
   * Find always returns the most recent value that maps to a key
   *)
  Axiom find_add :
    forall {val : Set} k v l,
      @find val k (add k v l) = Some v.

  (*
   * Removing a key from the empty map returns the empty map
   *)
  Axiom remove_empty :
    forall {val : Set} k,
      @remove val k empty = empty.

  (*
   * Remove is a kind of inverse of add
   *)
  Axiom remove_add :
    forall {val : Set} k v l,
      @remove val k (add k v l) = l.

  (*
   * If a key is not in the map, then removing it does nothing
   *)
  Axiom remove_not_found :
    forall {val : Set} k l,
      find k l = None ->
      @remove val k l = l.

End MAP.

(*
 * Your task is to implement the map ADT using association lists.
 *
 * You may change any of the Definition statements to Fixpoint, and you may use
 * existing standard library functions.
 *
 * If your proofs do not go through, consider the possibility that the functions
 * you have defined are incorrect. For example, I implemented remove incorrectly
 * the first time around, which made remove_not_found unprovable.
 *)

Module AssociationList (s : SET_WITH_EQUALITY) : MAP s.
  Definition key := s.t. (* The type of keys *)
  Definition t (val : Set) := list (key * val). (* A list of key-value pairs *)
  Definition empty {val : Set} : t val := nil. (* The empty map is an empty list *)

  (* --- Basic operations --- *)

  (*
   * Problem 1 [5 points, ~2 LOC]: Implement the find function.
   *
   * Hint: The boolean equality function s.equal will be helpful here.
   *)
  Definition find {val : Set} (k : key) (l : t val) : option val :=
    None. (* YOUR CODE HERE *)

  (*
   * Problem 2 [5 points, ~2 LOC]: Implement the add function.
   *)
  Definition add {val : Set} (k : key) (v : val) (l : t val) : t val :=
    l. (* YOUR CODE HERE *)

  (*
   * Problem 3 [5 points, ~5 LOC]: Implement the remove function.
   *
   * Hint: The boolean equality function s.equal will be helpful here.
   *)
  Fixpoint remove {val : Set} (k : key) (l : t val) : t val :=
    l. (* YOUR CODE HERE *)

  (* --- Specifications for basic operations --- *)

  (*
   * Problem 4 [5 points, ~2 tactics]: Prove find_empty.
   *)
  Theorem find_empty :
    forall {val : Set} k,
      @find val k empty = None.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 5 [10 points, ~10 tactics]: Prove find_add.
   *
   * Hint: See the proof of decideable_equality in ListSet in DataAbstraction.v
   * for a technique to destruct on whether s.equal holds on two values.
   *)
  Theorem find_add :
    forall {val : Set} k v l,
      @find val k (add k v l) = Some v.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 6 [5 points, ~2 tactics]: Prove remove_empty.
   *)
  Theorem remove_empty :
    forall {val : Set} k,
      @remove val k empty = empty.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 7 [10 points, ~10 tactics]: Prove remove_add.
   *)
  Theorem remove_add :
    forall {val : Set} k v l,
      @remove val k (add k v l) = l.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 8 [15 points, ~15 tactics]: Prove remove_not_found.
   *)
  Theorem remove_not_found :
    forall {val : Set} k l,
      find k l = None ->
      @remove val k l = l.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

End AssociationList.

(*
 * We can instantiate this with specific types now, like natural numbers:
 *)

Module NatAssociationList := AssociationList NatWithEquality.

(*
 * We now have an ADT and an implementation of the ADT.
 * To make sure our ADT is actually useful, it helps to have a client as well.
 *
 * Below, we define graphs as association lists using the map ADT.
 * Your task is to prove a few theorems about these graphs.
 *
 * Hint: It will help to use the lemmas from the map ADT.
 *)

Module Graph (s : SET_WITH_EQUALITY) (m : MAP s).
  Definition empty := @m.empty (list s.t). (* The empty graph *)

  (*
   * Get all vertices adjacent to v in g.
   *)
  Definition adjacent (v : s.t) (g : m.t (list s.t)) : list s.t :=
    match m.find v g with
    | Some l => l
    | None => []
    end.

  (*
   * Add edges from v1 to every vertex in v2s to g.
   *)
  Definition add_adjacent (v1 : s.t) (v2s : list s.t) (g : m.t (list s.t)) : m.t (list s.t) :=
    m.add v1 v2s g.

  (*
   * Remove all edges from v in g.
   *)
  Definition remove_adjacent (v : s.t) (g : m.t (list s.t)) : m.t (list s.t) :=
    m.remove v g.

  (*
   * Problem 9 [5 points, ~5 tactics]: Prove adjacent_empty.
   *)
  Theorem adjacent_empty :
    forall v,
      adjacent v empty = [].
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 10 [5 points, ~5 tactics]: Prove adjacent_add.
   *)
  Theorem adjacent_add :
    forall v1 v2s g,
      adjacent v1 (add_adjacent v1 v2s g) = v2s.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 11 [5 points, ~3 tactics]: Prove remove_empty.
   *)
  Theorem remove_empty :
    forall v,
      remove_adjacent v empty = empty.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * Problem 12 [5 points, ~2 tactics]: Prove remove_add_adjacent.
   *)
  Theorem remove_add_adjacent :
    forall v1 v2s g,
      remove_adjacent v1 (add_adjacent v1 v2s g) = g.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (* --- BONUS PROBLEM --- *)

  (*
   * We've encoded graph reachability as both an inductive relation (Reachable)
   * and a fixpoint (reachable). Your task is to prove the correspondence between
   * the two.
   *)

  Inductive Reachable (g: m.t (list s.t)) : s.t -> s.t -> Prop :=
  | ReachRefl :
      forall x,
      Reachable g x x
  | ReachTrans :
      forall x y z,
      In y (adjacent x g) ->
      Reachable g y z ->
      Reachable g x z.

  Fixpoint reachable' (fuel : nat) (g : m.t (list s.t)) (wl : list s.t) (b : s.t) : option bool :=
    match fuel with
    | O => None
    | S fuel' =>
        match wl with
        | [] => Some false
        | x :: xs =>
            if s.equal x b
            then Some true
            else reachable' fuel' g (xs ++ adjacent x g) b
        end
     end.

  Definition reachable (g : m.t (list s.t)) (a b : s.t) : option bool :=
    reachable' 1000 g [a] b.

  (*
   * BONUS [15 points, ~25 tactics]: Prove the correspondence between
   * reachable' and Reachable.
   *
   * Hint: The proof for this will mirror the structure of reachable'.
   *)
  Lemma reachable'_Reachable:
    forall n g wl b,
      reachable' n g wl b = Some true ->
      exists a, In a wl /\ Reachable g a b.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

  (*
   * BONUS [5 points, ~10 tactics]: Using reachable'_Reachable,
   * prove the correspondence between reachable and Reachable.
   *)
  Theorem reachable_Reachable:
    forall g a b,
      reachable g a b = Some true ->
      Reachable g a b.
  Proof.
    (* YOUR PROOF HERE *)
  Admitted. (* CHANGE TO QED *)

End Graph.
