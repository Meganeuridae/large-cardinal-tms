(** Fresh variable assignments preserve every older name and expose each
    newly bound value at its allocated index. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics.
Import ListNotations.

Fixpoint push_environment {D : Type} (rho : nat->D) next (values : list D) : nat->D :=
  match values with
  | [] => rho
  | x::xs => push_environment (update_variable rho next x) (S next) xs
  end.

Lemma push_environment_old {D} (rho:nat->D) next values i : i<next ->
  push_environment rho next values i = rho i.
Proof.
  revert rho next. induction values as [|x xs IH]; intros rho next H; cbn [push_environment].
  - reflexivity.
  - rewrite IH by lia. apply update_variable_neq. lia.
Qed.

Lemma push_environment_at {D} (rho:nat->D) next values k value :
  nth_error values k = Some value -> push_environment rho next values (next+k) = value.
Proof.
  revert rho next k. induction values as [|x xs IH]; intros rho next [|k] H; cbn [nth_error] in H;
    try discriminate.
  - inversion H; subst. cbn [push_environment]. rewrite Nat.add_0_r.
    rewrite push_environment_old by lia. apply update_variable_eq.
  - cbn [push_environment]. replace (next+S k) with (S next+k) by lia. now apply IH.
Qed.

Print Assumptions push_environment_old.
Print Assumptions push_environment_at.
