Require Import Frap Frap.Imp.

(*
 * CSE505 Homework 5.
 *
 * I'm supposed to give a demo of a program I wrote next week to some folks at UCSD.
 * Unfortunately, the demo isn't working, because the compiler I used to compile my program had a bug!
 *
 * For some reason, I noticed that when I compile programs, it switches the if and else branches.
 * The compiler isn't open source, so I can't just go fix the bug.
 * I noticed, though, that I can probably define a program transformation that I can run on programs before I compile them,
 * and then my compiler should do the right thing.
 *
 * But I want to be totally positive this transformation works, because I don't want to give a bad demo.
 * Can you help me write that program transformation, and prove that it's correct?
 *
 * The language my compiler operates over is the cmd language from FRAP (see Frap/Imp.v), which I'll
 * print here for convenience:
 *)

(* --- Syntax --- *)

Print arith. (* arithmetic expressions *)
Print cmd. (* commands *)

(* --- Semantics --- *)

Print valuation. (* maps from variables to values *)
Print interp. (* interpreter for arithmetic expression *)

Print eval. (* big-step semantics *)
Print step. (* small-step semantics *)

(* --- Part 1: Buggy semantics --- *)

(*
 * The first thing we need to do is define the semantics of my buggy compiler.
 * We'll want both big-step sematics (like eval) and small-step semantics (like step).
 *
 * BE CAREFUL HERE!
 *
 * Remember that the semantics are part of the TCB, so it's possible to get
 * this wrong and then make the proofs later below much too easy or too hard!
 * Make sure to carefully read the description of what these semantics should
 * capture and get it right!
 *)

(*
 * Problem 1 [5 points, ~25 loc]: Define eval_buggy,
 * the big-step semantics of my buggy compiler.
 *
 * Hint: This should look similar to eval, but adjusted for
 * the bugs in my compiler.
 *)
Inductive eval_buggy : valuation -> cmd -> valuation -> Prop :=
. (* YOUR CODE HERE *)

(*
 * Problem 2 [5 points, ~20 loc]: Define step_buggy,
 * the small-step semantics of my buggy compiler.
*
 * Hint: This should look similar to step, but adjusted for
 * the bugs in my compiler.
 *)
Inductive step_buggy : valuation * cmd -> valuation * cmd -> Prop :=
. (* YOUR CODE HERE *)

(* --- Program transformation --- *)

(*
 * Phew, now that we understand what the buggy compiler is doing,
 * let's think about our program transformation.
 *
 * Before we define the transformation, we'd like to know what
 * makes the transformation correct. Ideally we'd like that if we were to run the command
 * c on the good compiler and get some result, then we can transform c to c' and run our buggy compiler
 * and get the same result. In other words:
 *)
Definition transformation_is_correct (f : cmd -> cmd) :=
  forall v c v',
    eval v c v' ->
    eval_buggy v (f c) v'.

(*
 * But it's really hard to prove things over eval because of while loops.
 * So we'll actually show this by making sure our transformation function
 * is correct at every single step:
 *)
Definition transformation_steps_correctly (f : cmd -> cmd) :=
  forall p1 p2,
    step p1 p2 ->
    step_buggy (fst p1, f (snd p1)) (fst p2, f (snd p2)).

(*
 * That will be sufficient to prove our transformation is correct later.
 * OK, now that we know what it means for it to be correct, let's define a function that
 * meets this criteria.
 *
 * Problem 3 [5 points, ~10 loc]: Define transform, a function that satisfies
 * transformation_steps_correctly and transformation_is_correct. We'll prove it's correct later.
 *)
Fixpoint transform (c : cmd) : cmd :=
  match c with
  (* YOUR CODE HERE *)
  | _ => c
  end.

(*
 * Before moving on, I recommend checking our transform function on a few examples.
 * If that looks good, let's move on.
 *
 * As I'm sure you know by now, sometimes it's too hard to prove things
 * about functions, so it's nice to have an inductive relation that corresponds to that
 * function. Doing this will make our proofs easier later.
 *
 * Problem 4 [5 points, ~15 loc]: Define Transform, a relation
 * that corresponds to transform. That is, the transform_Transform
 * and Transform_transform theorems below should both be provable.
 *)
Inductive Transform  : cmd -> cmd -> Prop :=
. (* YOUR CODE HERE *)

(*
 * Now let's show that our relation is correct.
 *
 * Problem 5 [5 points, ~20 tactics]: Prove transform_Trasform.
 *
 * Hint: Be careful not to introduce too eagerly.
 *)
Theorem transform_Transform:
  forall c1 c2,
    transform c1 = c2 ->
    Transform c1 c2.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * Problem 6 [5 points, ~10 tactics]: Prove Trasform_transform.
 *
 * Hint: This will probably be easier if you induct over the Transform relation.
 *)
Theorem Transform_transform:
  forall c1 c2,
    Transform c1 c2 ->
    transform c1 = c2.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* --- Transformation steps correctly --- *)

(*
 * Great! Now, we want to prove our transformation correct.
 * As I mentioned earlier, we'll show transformation_steps_correctly.
 * But showing that directly is difficult, so let's show it over
 * our Transform relation instead.
 *
 * First, let's just show that if we can take a step in a correct compiler,
 * and we can transform that program into another program,
 * and we can take a step in our buggy compiler from the transformed program,
 * then the program we step to in our buggy compiler will be the transformation
 * of the program we would step to in a correct compiler.
 *
 * In other words, let's fill in the bottom arrow in this diagram:
 *
 * p1 ---Transform----> p1'
 *  |                   |
 *  |                   |
 * step             step_buggy
 *  |                   |
 *  V                   V
 * p2 ---Transform----> p2'
 *
 * Problem 7 [20 points, ~75 tactics]: Prove lock_step.
 * This looks a little weird because our programs are pairs (v, c) : valuation * cmd.
 *
 * Hint: Like in problems 5 and 6, make sure you think about what you induct over
 * and how eagerly you introduce so that your inductive hypothesis is strong enough
 * to prove your goal. Otherwise, you'll run into trouble.
 *)
Lemma lock_step:
  forall p1 p2,
    step p1 p2 ->
    forall c1' c2',
      Transform (snd p1) c1' ->
      step_buggy (fst p1, c1') (fst p2, c2') ->
      Transform (snd p2) c2'.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * OK, so now we have a good result that holds as long as we an always take a step with our
 * buggy compiler. But we can't use that to show transformation_steps_correctly
 * without showing that we can actually take such a step. If the step_buggy arrow doesn't
 * exist, then we're stuck in this state:
 *
 * p1 ---Transform----> p1'
 *  |
 *  |
 * step
 *  |
 *  V
 * p2 ---Transform----> p2'
 *
 * And that's not very useful. So let's fill in the right arrow.
 *
 * Problem 8 [15 points, ~50 tactics]: Prove step_step_buggy.
 *)
Lemma step_step_buggy:
  forall p1 p2,
    step p1 p2 ->
    forall c1',
      Transform (snd p1) c1' ->
      exists c2',
        step_buggy (fst p1, c1') (fst p2, c2').
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * Great! Now we can show our Transform relation steps correctly.
 * I'll take care of this one, since you've done all of the hard work already.
 *)
Theorem Transform_steps_correctly:
  forall p1 p2,
    step p1 p2 ->
    forall c1',
      Transform (snd p1) c1' ->
      exists c2',
        step_buggy (fst p1, c1') (fst p2, c2') /\
        Transform (snd p2) c2'.
Proof.
  intros. pose proof (step_step_buggy p1 p2 H c1' H0).
  destruct H1. exists x. split; auto.
  eapply lock_step; eauto.
Qed.

(*
 * We can then use Transform_steps_correctly to prove our transformation function correct.
 *
 * This proof should be pretty small, but since you're doing all of the hard work,
 * you should get the satisfaction of the Qed, so I'll sit this one out.
 *
 * Problem 9 [10 points, ~10 tactics]: Prove transform_steps_correctly.
 *
 * Hint: Use the relationship between transform and Transform that you proved earlier.
 *)
Theorem transform_steps_correctly:
  transformation_steps_correctly transform.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* --- Transitive closure --- *)

(*
 * We know our transformation function is correct over a single step.
 * Now let's prove it over the transitive closure!
 *
 * If you look at the Imp development in FRAP, you'll notice that the transitive
 * closure of the step relation is defined:
 *)
Check step^*.

(*
 * Similarly, we can get the transitive closure of step_buggy:
 *)
Check step_buggy^*.

(*
 * Both of these use a type called trc:
 *)
Print trc.

(*
 * Importantly, trc is inductive. Familiarize yourself with the two cases,
 * if you're not familiar with them already.
 *)

(*
 * Once you've done that, let's prove the result over the transitive closure.
 *
 * Problem 10 [10 points, ~10 tactics]: Prove transform_steps_correctly_star.
 *
 * Hint: Choose what you induct over wisely, and use the result you've
 * already proven over a single step.
 *)
Theorem transform_steps_correctly_star:
  forall p1 p2,
    step^* p1 p2 ->
    step_buggy^* (fst p1, transform (snd p1)) (fst p2, transform (snd p2)).
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(* --- Relating the transitive closure and eval --- *)

(*
 * I think we're really getting somewhere. All we need now to tie this back
 * to our eval and eval_buggy relation is a way to relate step^* to eval and
 * step_buggy^* to eval_buggy^*. Adam Chlipala was nice enough to do these proofs
 * for us for the correct compiler in Imp.v:
 *)
Check step_star_Seq.
Check big_small.
Check small_big.

(*
 * I think if we follow his approach, we'll have no trouble proving this
 * for eval_buggy, so let's give it a shot. I've started by copying and
 * pasting his proof scripts, but they don't quite go through.
 * Can you fix them so they do?
 *
 * Problem 11 [10 points]: Fix any proofs below that are broken
 * so that they work with your step_buggy and eval_buggy relations.
 *)
Lemma step_star_Seq_buggy : forall v c1 c2 v' c1',
  step_buggy^* (v, c1) (v', c1')
  -> step_buggy^* (v, Sequence c1 c2) (v', Sequence c1' c2).
Proof.
  induct 1.

  constructor.

  cases y.
  econstructor.
  econstructor.
  eassumption.
  apply IHtrc.
  equality.
  equality.
Qed.

Theorem big_small_buggy : forall v c v', eval_buggy v c v'
  -> step_buggy^* (v, c) (v', Skip).
Proof.
  induct 1; simplify.

  constructor.

  econstructor.
  constructor.
  constructor.

  eapply trc_trans.
  apply step_star_Seq_buggy.
  eassumption.
  econstructor.
  apply StepSeq2'.
  assumption.

  econstructor.
  apply StepIfFalse'.
  assumption.
  assumption.

  econstructor.
  constructor.
  assumption.
  assumption.

  econstructor.
  constructor.
  assumption.
  eapply trc_trans.
  apply step_star_Seq_buggy.
  eassumption.
  econstructor.
  apply StepSeq2'.
  assumption.

  econstructor.
  apply StepWhileFalse'.
  assumption.
  constructor.
Qed.

Lemma small_big_buggy'' : forall v c v' c', step_buggy (v, c) (v', c')
                                      -> forall v'', eval_buggy v' c' v''
                                                     -> eval_buggy v c v''.
Proof.
  induct 1; simplify.

  invert H.
  constructor.

  invert H0.
  econstructor.
  apply IHstep_buggy.
  eassumption.
  assumption.

  econstructor.
  constructor.
  assumption.

  apply EvalIfFalse'.
  assumption.
  assumption.

  constructor.
  assumption.
  assumption.

  invert H0.
  econstructor.
  assumption.
  eassumption.
  assumption.

  invert H0.
  apply EvalWhileFalse'.
  assumption.
Qed.

Lemma small_big_buggy' : forall v c v' c', step_buggy^* (v, c) (v', c')
                                     -> forall v'', eval_buggy v' c' v''
                                                    -> eval_buggy v c v''.
Proof.
  induct 1; simplify.

  trivial.

  cases y.
  eapply small_big_buggy''.
  eassumption.
  eapply IHtrc.
  equality.
  equality.
  assumption.
Qed.

Theorem small_big_buggy : forall v c v', step_buggy^* (v, c) (v', Skip)
                                   -> eval_buggy v c v'.
Proof.
  simplify.
  eapply small_big_buggy'.
  eassumption.
  constructor.
Qed.

(* --- Final proof of correctness of transform --- *)

(*
 * Great! We're almost done.
 *
 * Now we can do our final proof. It should be easy!
 * We should be able to just apply the result we had over the transitive closure of the relation,
 * transform_steps_correctly_star, now that we have a correspondence between the big and small
 * step semantics.
 *
 * Problem 12 [5 points, ~10 tactics]: Prove transform_is_correct.
 *)
Theorem transform_is_correct:
  transformation_is_correct transform.
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* CHANGE TO QED *)

(*
 * Thank you so much! I can now feel that much more certain that my demo will work!
 *)


(* BONUS CHALLENGE PROBLEMS:

  1. Are there other transformations you could use to still
     get code to behave correctly under the buggy semantics?
     Try to design a transformation that fixes code to run
     in the wonky, "flipped conditional" semantics that only
     changes expressions in branches and leaves the if and then
     expressions where they are instead.

  2. Zach has an even stranger computer: instead of flipping
     branches, it runs Seq commands under a reversed time machine!
     That is for a command like:
         c1; c2; c3; c4
     it would first run c4 then c3 then c2 then c1.  Model this
     flaw in another semantics and design a transformation to
     correctly handle this weird temporal bug.  Can you prove
     your transformation correct?

  3. For any or all of the above transformations, also try
     proving the corresponding backward simulation.

*)
