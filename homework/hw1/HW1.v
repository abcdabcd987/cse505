(* --- Homework 1: Introduction to Coq --- *)

(*
 * This homework is a tutorial introduction to Coq.
 * It does not correspond to any chapter in FRAP.
 * Step through this with CoqIde (or another IDE for Coq),
 * then fill in the problems that are not yet done.
 *)

(* --- Setting up Coq and FRAP --- *)

(*
 * PROBLEM 0: Your first step will be setting up Coq 8.8 and FRAP.
 * Instructions for this can be found in README.md in this directory.
 *
 * Once Coq and FRAP are both installed according to directions,
 * the following line should work:
 *)

Require Import Frap.
(*
 * That `Require Import` line is called a command.
 * Commands start with capital letters and do things like print terms and
 * compute results. We'll see more of those soon.
 *)

(* --- Learning the Gallina programming language --- *)

(*
 * With Coq set up, you can now write some simple programs.
 * The programming language for Coq is called Gallina.
 *
 * Datatypes in Gallina can be defined in cases, using something
 * called inductive types, which you'll learn more about later.
 * For example, here is a type representing booleans:
 *)
Print bool. (* `Print` is a command that prints a term *)
(*
 * Inductive bool : Set :=
 * | true : bool   (* true is a boolean, and *)
 * | false : bool. (* false is a boolean *)
 *
 * We can reference each of these cases:
 *)
Eval compute in true. (* `Eval compute` is a command that fully simplifies a term *)
Eval compute in false.

(*
 * Inductive types can also refer to themselves.
 * Consider the natural numbers {0, 1, 2, ....}:
 *)
Print nat.
(*
 * Inductive nat : Set :=
 * | O : nat         (* Zero is a natural number, and *)
 * | S : nat -> nat. (* the successor of a natural number is a natural number *)
 *)
Eval compute in O.
Eval compute in (S (S O)).
Eval compute in 0. (* built-in syntax for O *)
Eval compute in 2. (* built-in syntax for (S (S O)) *)

(*
 * Gallina also has some language constructs you may be familiar with,
 * like constants:
 *)
Definition zero : nat := 0.
Print zero. (* 0 : nat *)
(*
 * functions:
 *)
Definition id_nat (n : nat) : nat := n.
Eval compute in (id_nat 5). (* 5 : nat *)
(*
 * types:
 *)
Definition id_T (T : Type) (t : T) : T := t.
Eval compute in (id_T nat 5). (* 5 : nat *)
(*
 * pattern matching:
 *)
Definition isZero (n : nat) : bool :=
  match n with
  | 0 => true
  | S _ => false
  end.
Eval compute in (isZero 0). (* true *)
Eval compute in (isZero 5). (* false *)
(*
 * recursive functions (with some restrictions):
 *)
Fixpoint isEven (n : nat) : bool :=
  match n with
  | 0 => true           (* 0 is even *)
  | 1 => false          (* 1 is not even *)
  | S (S p) => isEven p (* for any p, S (S p) is even iff p is even *)
  end.
Eval compute in isEven 0. (* true *)
Eval compute in isEven 1. (* false *)
Eval compute in isEven 6. (* true *)
Eval compute in isEven 7. (* false *)

Fixpoint myAdd (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m                (* 0 + m = m *)
  | S p => S (myAdd p m)  (* (S p) + m = S (p + m) *)
  end.
Eval compute in (myAdd 0 0). (* 0 : nat *)
Eval compute in (myAdd 6 4). (* 10 : nat *)
Eval compute in (fun m => myAdd 0 m). (* (fun m : nat => m) : nat -> nat *)
(*
 * and more. These are the core features you will need, for now.
 *)

(*
 * PROBLEM 1 [25 points]: Write a function isSucc that returns true if
 * a natural number is a successor of some other number, and false otherwise.
 *)
Definition isSucc (n : nat) := true. (* YOUR CODE HERE *)

(* sanity tests: *)
Eval compute in isSucc 0. (* should be false *)
Eval compute in isSucc 1. (* should be true *)
Eval compute in isSucc 6. (* should be true *)

(*
 * PROBLEM 2 [25 points]: Write a function isThreeven that returns true if
 * a natural number is a multiple of three (including zero), and false otherwise.
 *)
Fixpoint isThreeven (n : nat) := true. (* YOUR CODE HERE *)

(* sanity tests: *)
Eval compute in isThreeven 0. (* should be true *)
Eval compute in isThreeven 1. (* should be false *)
Eval compute in isThreeven 2. (* should be false *)
Eval compute in isThreeven 3. (* should be true *)
Eval compute in isThreeven 4. (* should be false *)
Eval compute in isThreeven 5. (* should be false *)
Eval compute in isThreeven 6. (* should be true *)

(* --- Learning the Ltac proof language --- *)

(*
 * Once you have written programs, you can prove things about them.
 * The language that you write proofs in is called Ltac.
 *
 * Ltac is a language of tactics, which guide Coq toward your goal state.
 * Here is a proof, for example, that two is even:
 *)
Lemma twoIsEven:
  isEven 2 = true.
Proof.
  reflexivity.
Qed.
(*
 * The `reflexivity` tactic says that `Eval compute in (isEven 2)`
 * is exactly true:
 *)
Eval compute in (isEven 2). (* true : bool *)
(*
 * You can also use `auto`, which is a little bit smarter sometimes:
 *)
Lemma twoIsEven':
  isEven 2 = true.
Proof.
  auto.
Qed.

(*
 * What each of these tactics is really doing is telling Coq to search
 * for a proof of your goal. The proofs that Coq finds are actually
 * just terms in Gallina, whose type are the goal you are trying to prove.
 * For example, we can also write a proof of twoIsEven by hand, without using Ltac:
 *)
Definition twoIsEven'' : isEven 2 = true :=
  eq_refl.
(*
 * The proof term here is eq_refl, which says that any term is equal to itself.
 * The type is (isEven 2 = true), which is the goal we are trying to prove.
 *
 * If we print the term that Coq found for us, we'll get the same thing:
 *)
Print twoIsEven. (* twoIsEven = eq_refl : isEven 2 = true *)
(*
 * Ltac just abstracts this away from you.
 *)

(*
 * An interesting consequence of this is that every term that
 * you write is also a proof of something, although often not a very
 * useful proof. For example, here are some proofs that if we have
 * a natural number, we can always produce another natural number:
 *)
Definition natNat1 (n : nat) : nat := n.
Definition natNat2 (n : nat) : nat := S n.
Definition natNat3 (n : nat) : nat := S (S n).
(*
 * As you can see, there are infinitely many ways to prove this fact.
 * If all we care about is the theorem being true,
 * we might not care about which proof we write.
 * When you end a proof in `Qed`, this is what you are saying:
 *)
Theorem natNat:
  nat ->
  nat.
Proof.
  apply natNat3. (* natNat3 proves this goal *)
Qed. (* I don't care how we showed nat -> nat, I just want to show it's true *)
Eval compute in (natNat 5). (* note how Coq doesn't call natNat3 here *)
(*
 * If for whatever reason you do care about which proof you used, you can write `Defined`
 * instead of `Qed`. This can be useful if you want Coq to write functions for you,
 * like isZero from earlier:
 *)
Definition isZero' (n : nat) : bool.
Proof.
  destruct n.           (* match n with *)
  - apply true.         (* | 0 => true *)
  - apply false.        (* | S _ => false *)
Defined.                (* end. *)

(*
 * Obviously, nat -> nat and nat -> bool are not very interesting facts to prove.
 * We can show more interesting things using the forall quantifier, like that our
 * isZero functions behave the same way:
 *)
Theorem isZero_isZero' :
  forall (n : nat),
    isZero n = isZero' n.
Proof.
  intros n.    (* in English, "let n be an arbitrary natural number" *)
  reflexivity. (* then these are exactly the same *)
Qed.
(*
 * nat -> nat is actually just shorthand for (forall (_ : nat), nat),
 * where _ is a variable whose name you don't care about.
 * So all of these behave the same way:
 *)
Definition natNat1' (n : nat) : nat := n.
Definition natNat1'' : forall (_ : nat), nat := fun (n : nat) => n.
Definition natNat1''' : nat -> nat := fun (n : nat) => n.
Theorem natNat1s:
  forall (n : nat),
    natNat1' n = natNat1'' n /\
    natNat1'' n = natNat1''' n.
Proof.
  intros n. split. (* break up the /\ into two cases *)
  - reflexivity.
  - reflexivity.
Qed.
(*
 * If you have multiple cases that look identical, you can use the semicolon to dispatch
 * these all at once:
 *)
Theorem natNat1s':
  forall (n : nat),
    natNat1' n = natNat1'' n /\
    natNat1'' n = natNat1''' n.
Proof.
  intros n. split; reflexivity. (* both cases are handled by reflexivity *)
Qed.

(*
 * Now we will do some slightly more interesting proofs.
 * This simple proof states that is n is even, then so is the successor
 * of the successor of n.
 *)

Theorem isEven_succ_succ:
  forall n,
    isEven n = true ->
    isEven (S (S n)) = true.
Proof.
  intros. simpl. apply H. (* holds by the hypothesis *)
Qed.

(*
 * PROBLEM 3 [25 points]: prove that if n is threeven,
 * then (S (S (S n))) is also threeven.
 *)
Theorem isThreeven_succ_succ_succ:
  forall n,
    isThreeven n = true ->
    isThreeven (S (S (S n))) = true.
Proof.
(* YOUR CODE HERE *)
Admitted. (* Change to QED when done *)

(*
 * We can prove much richer specifications than this,
 * but we leave that to later homeworks.
 *)

(* --- Induction --- *)

(*
 * Just like we can recurse inside of functions, we can recurse inside of proofs.
 * In that case, we want to use `induction` instead of `destruct`.
 * So, for example, an alternative way to define myAdd from above is this way:
 *)
Theorem myAdd' (n : nat) (m : nat) : nat.
Proof.
  induction n.          (* match n with *)
  - apply m.            (* | 0 => m *)
  - apply S. apply IHn. (* | S p => S (myAdd' p m) *)
Defined.                (* end. *)
(*
 * IHn here is the inductive hypothesis, which just means that it corresponds to the recursive call.
 * If you print this, it looks different from the manual version for technical reasons,
 * but the behavior is the same, and we can prove this using `induction` as well:
 *)
Theorem myAdd_myAdd' :
  forall n m,
    myAdd n m = myAdd' n m.
Proof.
  intros n m. induction n.
  - reflexivity.
  - simpl. rewrite IHn. (* `rewrite` substitutes in an equality *)
    reflexivity.
Qed.

(*
 * PROBLEM 4 [25 points]: Prove that myAdd n 1 = (S n).
 * This will look a lot like myAdd_myAdd'.
 *)
Theorem myAdd_one_right:
  forall (n : nat),
    myAdd n 1 = S n.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to QED when done *)

(* --- Summary --- *)

(*
 * There's a lot more to learn about Coq, but hopefully this got you
 * used to the basics.
 *
 * To submit your homework, please follow the instructions at the end
 * of the README.md file in this directory.
 *)
