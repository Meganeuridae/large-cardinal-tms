(** Alpha-equivalences in the rename-stable logical fragment. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula LogicBridge LogicFresh TheoryIrreflexiveND FormulaRenaming
  AugmentedLogic AugmentedCapture StableLogic StableInstantiation StableCapture StableCongruence.
Import ListNotations.
Lemma stable_all_alpha_forward x y p : nd_not_bound y p=true -> nd_free y p=false ->
  RenameStable (FImp (FAll x p) (FAll y (nd_subst x y p))).
Proof.
  intros Bound Free. destruct (Nat.eq_dec x y) as [E|E].
  - subst y. rewrite nd_subst_self. apply stable_logical,logical_identity.
  - apply stable_fresh_generalization.
    + apply nd_free_not_occurs. cbn [nd_free]. apply Nat.eqb_neq in E.
      rewrite Nat.eqb_sym,E. exact Free.
    + apply stable_all_instantiate_safe,nd_not_bound_implies_safe,Bound.
Qed.
Theorem stable_alpha_equiv x y p : nd_not_bound y p=true -> nd_free y p=false ->
  StableEquiv (FAll x p) (FAll y (nd_subst x y p)).
Proof. intros Bound Free. split; [now apply stable_all_alpha_forward|now apply stable_all_alpha_reverse]. Qed.
Lemma stable_equiv_trans p q r : StableEquiv p q -> StableEquiv q r -> StableEquiv p r.
Proof.
  intros [PQ QP] [QR RQ]. split; eapply stable_syllogism; eassumption.
Qed.
Lemma stable_extract p : RenameStable p -> AugProvable p.
Proof.
  intro H. specialize (H (fun n=>n) ltac:(intros x y E;exact E)). now rewrite rename_identity in H.
Qed.
Print Assumptions stable_alpha_equiv.
Print Assumptions stable_extract.
