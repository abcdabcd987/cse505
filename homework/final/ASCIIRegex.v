(* --- CSE505 Final: A Verified Regular-Expression Matcher --- *)

(*
 * In this final, we will define a regular expression (regex) matcher,
 * and prove the regex matcher correct. 
 *
 * The final is organized into five parts:
 *
 * Part 1 [1 problem,  10 points]: Defining a regex match relation
 * Part 2 [2 problems, 20 points]: Proving properties of the regex match relation
 * Part 3 [2 problems, 20 points]: Matching the empty string
 * Part 4 [2 problems, 30 points]: Regex derivatives
 * Part 5 [2 problems, 20 points]: Building and proving a correct regex matcher,
 *                                 using code from the previous parts
 * ---------------------------------------------------------------------------
 * Total: 9 problems, 100 points
 *
 * There is a bonus problem at the end.
 * 
 * NOTE ON ACADEMIC INTEGRITY: You should not discuss this final with any
 * other student, nor should you consult any code that is not included,
 * with the exception of code from lectures, previous homeworks, FRAP,
 * and the Coq standard library. Doing either of these is a violation of the 
 * honor code.
 *)

(* --- Dependencies --- *)

(*
 * We have included Frap and StructTact for your convenience. You may use
 * any of the tactics from these libraries.
 *)
Require Import Frap.
Require Import StructTactics.

(*
 * Our regex matcher will match strings as defined in the Coq standard library:
 *)
Require Import String.
Require Import Strings.Ascii.
Print string.

(*
 * This has some useful syntax defined for us: 
 *)
Open Scope string_scope.
Check "". (* empty string *)
Check (fun (s1 s2  : string) => s1 ++ s2). (* append *)

(*
 * This line works around a confusing name collision with variables in Frap.
 *)
Notation string := string.

(* --- Part 1: Regex Matcher [1 problem, 10 points] --- *)

(*
 * This section is adapted from Software Foundations.
 *)

(* 
 * Regular expressions are a simple language for describing strings,
 * defined as follows: 
 *)
Inductive reg_exp : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : ascii -> reg_exp
| Dot : reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

(* 
 * Problem 1 [10 points, ~30 LOC]: Define exp_match, an inductive
 * relation that holds when a regular expression matches some string:
 *
 *   - The expression [EmptySet] does not match any string.
 *
 *   - The expression [EmptyStr] matches the empty string [[]].
 *
 *   - The expression [Char x] matches the one-character string [[x]].
 *
 *   - The expression [Dot] matches any ASCII character.
 *
 *   - If [re1] matches [s1], and [re2] matches [s2], then [App re1
 *     re2] matches [s1 ++ s2].
 *
 *   - If at least one of [re1] and [re2] matches [s], then [Union re1
 *     re2] matches [s].
 *
 *   - Finally, if we can write some string [s] as the concatenation of
 *     a sequence of strings [s = s_1 ++ ... ++ s_k], and the
 *     expression [re] matches each one of the strings [s_i], then
 *     [Star re] matches [s].
 *
 *     As a special case, the sequence of strings may be empty, so
 *     [Star re] always matches the empty string [[]] no matter what
 *     [re] is. 
 *)
Inductive exp_match : string -> reg_exp -> Prop :=
. (* YOUR CODE HERE *)

(*
 * At the same time, let's introduce a more readable infix notation:
 *)
Notation "s =~ re" := (exp_match s re) (at level 80).

(* --- Part 2: Properties of the Regex Match Relation [2 problems, 20 points] --- *)

(*
 * We have now defined a match relation over regular expressions and strings. 
 * We can use such a definition to manually prove that a given regex matches 
 * a given string, but it does not give us a program that we can run to 
 * determine a match auotmatically.
 *
 * We'll implement regex matching using an algorithm that operates purely on 
 * strings and regexes without defining and maintaining additional datatypes.
 * We'll then verify that its value reflects the match relation. 
 *)

(* 
 * The proof of correctness of the regex matcher will combine
 * properties of the regex-matching function with properties of the
 * [match] relation that do not depend on the matching function. We'll go
 * ahead and prove the latter class of properties now. Most of them have
 * straightforward proofs, which have been given to you, although there
 *  are a few key lemmas that are left for you to prove. 
 *)

(*
 * Each provable [Prop] is equivalent to [True]. 
 *)
Lemma provable_equiv_true : 
  forall (P : Prop), 
    P -> 
    (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(* 
 * Each [Prop] with a provable negation is equivalent to [False]. 
 *)
Lemma not_equiv_false : 
  forall (P : Prop), 
    ~P -> 
    (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. inversion H0.
Qed.

(*
 * [EmptySet] matches no string. 
 *)
Lemma null_matches_none : 
  forall (s : string), 
    (s =~ EmptySet) <-> False.
Proof.
  intros. 
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(*
 * [EmptyStr] only matches the empty string. 
 *)
Lemma empty_matches_eps : 
  forall (s : string), 
    s =~ EmptyStr <-> s = "".
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(*
 * [EmptyStr] matches no non-empty string. 
 *)
Lemma empty_nomatch_ne : 
  forall (a : ascii) (s : string), 
    (String a s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(* 
 * [Char a] matches no string that starts with a non-[a] character. 
 *)
Lemma char_nomatch_char :
  forall (a b : ascii) (s : string), 
    b <> a -> (String b s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed. 

(* 
 * If [Char a] matches a non-empty string, then the string's tail is empty. 
 *)
Lemma char_eps_suffix : 
  forall (a : ascii) (s : string), 
    String a s =~ Char a <-> s = "".
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(*
 * [App re0 re1] matches string [s] iff [s = s0 ++ s1], 
 * where [s0] matches [re0] and [s1] matches [re1]. 
 *)
Lemma app_exists : 
  forall (s : string) (re0 re1 : reg_exp),
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(* 
 * Problem 2 [10 points, ~50 tactics]: Prove app_ne, which shows that
 * [App re0 re1] matches [String a s] iff [re0] matches the empty string
 * and [String a s] matches [re1] or [s=s0++s1], where [String a s0] matches [re0]
 * and [s1] matches [re1].
 *
 * Even though this is a property of purely the match relation, it is a
 * critical observation behind the design of our regex matcher. So (1)
 * take time to understand it, (2) prove it, and (3) look for how you'll
 * use it later.
 *)
Lemma app_ne : 
  forall (a : ascii) (s : string) (re0 re1 : reg_exp),
    String a s =~ (App re0 re1) <->
    ("" =~ re0 /\ String a s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ String a s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* 
 * [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. 
 *)
Lemma union_disj : 
  forall (s : string) (re0 re1 : reg_exp),
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H. 
Qed.

(* 
 * Problem 3 [10 points, ~25 tactics]: Prove star_ne, which shows that 
 * [String a s] matches [Star re]  iff [s = s0 ++ s1], where [String a s0] 
 * matches [re] and [s1] matches [Star re]. Like [app_ne], this observation 
 * is critical, so understand it, prove it, and keep it in mind.
 *
 * Hint: You can use the [split] tactic to break <-> into two cases.
 * 
 * Hint: The [remember] tactic may be useful to generalize [String a s =~ Star re]
 * so that you can prove the right property by induction. Alternatively,
 * the [induct] tactic from Frap may be useful.
 *)
Lemma star_ne : 
  forall (a : ascii) (s : string) (re : reg_exp),
    String a s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ String a s0 =~ re /\ s1 =~ Star re.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* --- Part 3: Matching the Empty String [2 problems, 20 points] --- *)

(* 
 * The definition of our regex matcher will include three fixpoint
 * functions. The first function, given regex [re], will evaluate to a
 * value that reflects whether [re] matches the empty string. The
 * function will satisfy the following property:
 *)
Definition refl_matches_eps (m : reg_exp -> bool) :=
  forall (re : reg_exp), ("" =~ re) <-> (m re = true).

(*
 * Problem 4 [5 points, ~10 LOC]: Define match_eps, which tests if a given 
 * regex matches the empty string.
 *)
Fixpoint match_eps (re: reg_exp) : bool :=
  true. (* YOUR CODE HERE *)

(* 
 * Problem 5 [15 points, ~50 tactics]: Prove match_eps_refl, which shows that 
 * [match_eps] indeed tests if a given regex matches the empty string.
 *)
Lemma match_eps_refl : 
  refl_matches_eps match_eps.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * We'll define other functions that use [match_eps]. However, the only 
 * property of [match_eps] that you'll need to use in all proofs
 * over these functions is [match_eps_refl]. 
 *
 * In those proofs, it may help at some point to destruct over match_eps_refl.
 * The following tactic may be useful for that:
 *)
Ltac destruct_match_eps re :=
  pose proof (match_eps_refl re); destruct (match_eps re).

(* --- Part 4: Derivatives [2 problems, 30 points] --- *)

(*
 * The key operation that will be performed by our regex matcher will
 * be to iteratively construct a sequence of regex derivatives. 

 * For each character [a] and regex [re], the derivative of [re] on [a] is a regex
 * that matches all suffixes of strings matched by [re] that start with
 * [a]. That is, [re'] is a derivative of [re] on [a] if they satisfy the
 * following relation: 
 *)
Definition is_der (re : reg_exp) (a : ascii) (re' : reg_exp) :=
  forall s, String a s =~ re <-> s =~ re'.
(*
 * Think a lot about this definition before continuing, and make sure that
 * you understand it. It may help to write out some examples by hand.
 * In addition, there are some tests below that may help you understand
 * the desired behavior.
 *)

(* 
 * A function [d] derives strings if, given character [a] and regex [re], 
 * it evaluates to the derivative of [re] on [a]. I.e., [d] satisfies the 
 * following property: 
*)
Definition derives (d : ascii -> reg_exp -> reg_exp) := 
  forall a re, is_der re a (d a re).

(* 
 * Problem 6 [10 points, ~20 LOC]: Define derive so that it derives strings. 
 *
 * Hint: One possible implementation uses [match_eps] in some cases 
 * to determine if key regex's match the empty string. 
 *
 * Hint: You can use ascii_dec to determine whether or not two characters
 * are equal.
 *)
Fixpoint derive (a : ascii) (re : reg_exp) : reg_exp :=
  EmptySet. (* YOUR CODE HERE *)

(*
 * [derive] should pass the following tests. Each test establishes an
 * equality between an expression that will be evaluated by our regex
 * matcher and the final value that must be returned by the regex
 * matcher. 
 *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(** "c" =~ Char c *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(** "c" =~ Char d *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr  *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c) *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(** "c" =~ Star c *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d) *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c) *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(*
 * The following tests give some additional insight into the behavior of [derive].
 * You should fill these proofs in to test the behavior of your code before
 * continuing onward. It will also help to write your own tests to ensure
 * your definition of [derive] is correct before continuing on to the proof
 * of correctness of [derive].
 *)
Example test_der8 :
  "c" =~ (derive c (Star (Char c))).
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

Example test_der9 :
  "c" =~ (derive c (App (Star (Char c)) (Char c))).
Proof. 
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * Problem 7 [20 points, ~125 tactics]: Prove derive_corr, which shows that 
 * [derive] in fact always derives strings.
 *
 * Hint: The destruct_match_eps tactic defined in the previous section
 * may be useful here.
 * 
 * Hint: if your definition of [derive] applies [match_eps] to a
 * particular regex [re], then a natural proof will apply
 * [match_eps_refl] to [re] and destruct the result to generate cases
 * with assumptions that the [re] does or does not match the empty string.
 * 
 * Hint: You can save quite a bit of work by using lemmas proved
 * above. In particular, to prove many cases of the induction, you can
 * rewrite a [Prop] over a complicated regex (e.g., [s =~ Union re0 re1])
 * using lemmas given above that are logical equivalences.
 *)
Lemma derive_corr : 
  derives derive.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * We'll define the regex matcher using [derive]. However, the only
 * property of [derive] that you'll need to use in all proofs of
 * properties of the matcher is [derive_corr]. 
 *)

(* --- Part 5: A Correct Regex Matcher [2 problems, 20 points] --- *)

(*
 * A function [m] matches regexes if, given string [s] and regex [re],
 * it evaluates to a value that reflects whether [s] is matched by
 * [re]. That is, [m] holds the following property: 
 *)
Definition matches_regex (m : string -> reg_exp -> bool) : Prop :=
  forall (s : string) (re : reg_exp), 
    (s =~ re) <-> (m s re = true).

(*
 * Problem 8 [10 points, ~5 LOC]: Define regex_match so that it matches regexes.
 *
 * Hint: You may want to use the match_eps and derive functions
 * that you defined earlier. Think about how both of these functions
 * can be useful.
 *)
Fixpoint regex_match (s : string) (re : reg_exp) : bool :=
  true. (* YOUR CODE HERE *)

(*
 * Problem 9 [10 points, ~10 tactics]: Finally, prove regex_refl, 
 * which shows that [regex_match] in fact matches regexes.
 *
 * Hint: match_eps_refl and derive_corr may be useful here.
 *)
Theorem regex_refl : 
  matches_regex regex_match.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* ---  Using with the regex matcher --- *)

(*
 * Here are some examples of running the regex matcher.
 * You can continue to play with it below, if you'd like. 
 *)

Eval compute in (regex_match "abc" (App (Char "a") (App (Char "b") (Char "c")))).

(* --- Bonus Problem --- *)

(*
 * Bonus 1: Heavily-optimized regex matchers match a regex by translating a given
 * regex into a state machine and determining if the state machine
 * accepts a given string. Implemement such an algorithm, and verify that
 * its value reflects the match relation. 
 *)

(*
 * YOUR CODE AND PROOFS HERE
 *)

