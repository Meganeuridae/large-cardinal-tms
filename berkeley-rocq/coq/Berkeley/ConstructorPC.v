(** Program-counter identities used when a constructor subroutine returns,
    tests a countdown register, or continues its outer loop. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps.
Import ListNotations.

Lemma constructor_break0_trues k bits :
  break_pc 0 (repeat true k ++ false::bits) = Some (true::bits,k).
Proof. induction k; cbn [repeat app break_pc]; [reflexivity|now rewrite IHk]. Qed.

Lemma constructor_return_word prefix :
  return_word (true :: rev prefix ++ [false]) = prefix ++ [true].
Proof.
  unfold return_word.
  change (rev (removelast ((true :: rev prefix) ++ [false])) = prefix ++ [true]).
  rewrite removelast_last. cbn [rev]. now rewrite rev_involutive.
Qed.

Lemma constructor_child_return prefix k :
  break_pc 0 (rev (prefix ++ [false] ++ repeat true k) ++ [false]) =
    Some (true :: rev prefix ++ [false],k) /\
  return_word (true :: rev prefix ++ [false]) = prefix ++ [true].
Proof.
  split; [|apply constructor_return_word].
  rewrite !rev_app_distr, rev_repeat. cbn [rev].
  repeat rewrite app_nil_r. repeat rewrite <- app_assoc. cbn [app].
  apply constructor_break0_trues.
Qed.

(** A failed DEC immediately following the first child of a binary pair
    leaves that whole pair, by skipping the condition's zero and then
    performing the caller's usual return. *)
Lemma constructor_failed_test_return prefix out n :
  break_pc 0 (rev prefix ++ [false]) = Some(out,n) ->
  break_pc 1 (rev (prefix ++ [true;false]) ++ [false]) = Some(out,S(S n)).
Proof.
  intro H. rewrite rev_app_distr. cbn [rev app break_pc].
  now rewrite H.
Qed.

(** The pair loop's continue leaf is its third right branch. *)
Lemma constructor_outer_continue prefix :
  continue_pc 2 (rev (prefix ++ [true;true])) = Some(rev prefix,2).
Proof.
  rewrite rev_app_distr. cbn [rev app continue_pc].
  destruct (rev prefix); reflexivity.
Qed.

Lemma constructor_first_test_return prefix out n :
  break_pc 0 (rev prefix ++ [false]) = Some(out,n) ->
  break_pc 1 (rev (prefix ++ [false]) ++ [false]) = Some(out,S n).
Proof. intro H. rewrite rev_app_distr. cbn [rev app break_pc]. now rewrite H. Qed.

Lemma constructor_inner_test_zero prefix :
  break_pc 1 (rev (prefix ++ [true;true;false;false]) ++ [false]) =
    Some (true :: true :: true :: rev prefix ++ [false],1) /\
  return_word (true :: true :: true :: rev prefix ++ [false]) = prefix ++ [true;true;true].
Proof.
  split.
  - rewrite rev_app_distr. reflexivity.
  - unfold return_word.
    change (rev (removelast ((true::true::true::rev prefix) ++ [false])) = prefix ++ [true;true;true]).
    rewrite removelast_last. cbn [rev]. rewrite rev_involutive.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma constructor_unpair_continue_early prefix :
  continue_pc 2 (rev (prefix ++ [true;true;false])) = Some(rev prefix,3).
Proof.
  rewrite rev_app_distr. cbn [rev app continue_pc]. destruct (rev prefix); reflexivity.
Qed.
Lemma constructor_unpair_continue_late prefix :
  continue_pc 3 (rev (prefix ++ [true;true;true])) = Some(rev prefix,3).
Proof.
  rewrite rev_app_distr. cbn [rev app continue_pc]. destruct (rev prefix); reflexivity.
Qed.

Print Assumptions constructor_child_return.
Print Assumptions constructor_failed_test_return.
Print Assumptions constructor_outer_continue.
Print Assumptions constructor_first_test_return.
Print Assumptions constructor_inner_test_zero.
Print Assumptions constructor_unpair_continue_early.
Print Assumptions constructor_unpair_continue_late.
