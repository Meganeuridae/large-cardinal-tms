(** Formula congruence in the injective-renaming-stable fragment. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofPresentation LogicBridge LogicFresh
  TheoryIrreflexiveND StableLogic StableInstantiation.
Import ListNotations.
Definition StableEquiv p q := RenameStable (FImp p q) /\ RenameStable (FImp q p).
Lemma stable_equiv_refl p : StableEquiv p p.
Proof. split; apply stable_logical,logical_identity. Qed.
Lemma stable_weaken_theorem p e : RenameStable p -> RenameStable (FImp e p).
Proof. intro H. eapply stable_mp; [apply stable_logical,logical_b1|exact H]. Qed.
Lemma stable_truth : RenameStable nd_true.
Proof. unfold nd_true. apply stable_logical,logical_identity. Qed.
Lemma stable_equiv_neg p q : StableEquiv p q -> StableEquiv (FNeg p) (FNeg q).
Proof.
  intros [F B]. destruct (stable_inst_neg_substitution nd_true p q
    (stable_weaken_theorem _ _ F) (stable_weaken_theorem _ _ B)) as [H K].
  split; eapply stable_mp; [exact H|apply stable_truth|exact K|apply stable_truth].
Qed.
Lemma stable_equiv_imp p p' q q' : StableEquiv p p' -> StableEquiv q q' -> StableEquiv (FImp p q) (FImp p' q').
Proof.
  intros [PF PB] [QF QB]. destruct (stable_inst_imp_substitution nd_true p p' q q'
    (stable_weaken_theorem _ _ PF) (stable_weaken_theorem _ _ PB)
    (stable_weaken_theorem _ _ QF) (stable_weaken_theorem _ _ QB)) as [H K].
  split; eapply stable_mp; [exact H|apply stable_truth|exact K|apply stable_truth].
Qed.
Lemma stable_equiv_all x p q : StableEquiv p q -> StableEquiv (FAll x p) (FAll x q).
Proof. intros [F B]. split; now apply stable_all_monotone. Qed.
Lemma stable_instance_congruence f vars holes holes' :
  (forall n, StableEquiv (holes n) (holes' n)) ->
  StableEquiv (independent_instance vars holes f) (independent_instance vars holes' f).
Proof.
  intro Eq. induction f as [b x y|p IH|p IH q JH|x p IH|n]; cbn [independent_instance].
  - destruct b; apply stable_equiv_refl.
  - now apply stable_equiv_neg.
  - now apply stable_equiv_imp.
  - now apply stable_equiv_all.
  - apply Eq.
Qed.

Print Assumptions stable_instance_congruence.
