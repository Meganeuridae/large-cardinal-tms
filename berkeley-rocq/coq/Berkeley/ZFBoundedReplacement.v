(** Ordinary bounded-domain partial-functional Replacement is derivable from
    the guarded-D augmentation of the literal global-functional schema. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import ProofFormula TheoryIrreflexiveND AugmentedLogic StandardND StandardAugSound StandardAugEquivalence ZFProtected
  ZFBoundedReplacementCore.
Import ListNotations.

Definition replacement_image p := nd_ex 1 (FAll 2 (nd_iff (FMember 2 1)
  (nd_ex 3 (nd_and replacement_domain p)))).
Definition bounded_replacement p := FImp (replacement_bounded_unique p) (replacement_image p).

Lemma aug_equiv_and p p' q q' : AugEquiv p p' -> AugEquiv q q' -> AugEquiv (nd_and p q) (nd_and p' q').
Proof. intros P Q. unfold nd_and. apply aug_equiv_neg,aug_equiv_imp; [exact P|now apply aug_equiv_neg]. Qed.
Lemma aug_equiv_iff p p' q q' : AugEquiv p p' -> AugEquiv q q' -> AugEquiv (nd_iff p q) (nd_iff p' q').
Proof. intros P Q. unfold nd_iff. apply aug_equiv_and; apply aug_equiv_imp; assumption. Qed.
Lemma aug_equiv_ex x p q : AugEquiv p q -> AugEquiv (nd_ex x p) (nd_ex x q).
Proof. intro P. unfold nd_ex. apply aug_equiv_neg,aug_equiv_all,aug_equiv_neg,P. Qed.

Lemma augmented_guard_idempotent p : AugEquiv
  (nd_and replacement_domain (replacement_guard p)) (nd_and replacement_domain p).
Proof.
  unfold replacement_guard. split; apply standard_theorem_to_augmented; apply std_imp_intro.
  - eapply std_and_right. apply std_hyp. now left.
  - apply std_and_intro.
    + eapply std_and_left. apply std_hyp. now left.
    + apply std_hyp. now left.
Qed.
Lemma guarded_replacement_image_equiv p : AugEquiv (replacement_image (replacement_guard p)) (replacement_image p).
Proof.
  unfold replacement_image. apply aug_equiv_ex,aug_equiv_all,aug_equiv_iff; [apply aug_equiv_refl|].
  apply aug_equiv_ex,augmented_guard_idempotent.
Qed.

Theorem bounded_replacement_derivable p : nd_free 1 p=false -> AugProvable (bounded_replacement p).
Proof.
  intro Fresh. assert (GuardFresh : nd_free 1 (replacement_guard p)=false).
  { unfold replacement_guard,replacement_domain,nd_and. cbn [nd_free]. now rewrite Fresh. }
  pose proof (standard_theorem_to_augmented _ (bounded_unique_implies_guarded_global p)) as Antecedent.
  pose proof (conventional_replacement_derivable (replacement_guard p) GuardFresh) as Replacement.
  change (AugProvable (FImp (replacement_global_unique (replacement_guard p)) (replacement_image (replacement_guard p)))) in Replacement.
  pose proof (proj1 (guarded_replacement_image_equiv p)) as Image.
  unfold bounded_replacement. eapply aug_syllogism; [exact Antecedent|]. eapply aug_syllogism; eassumption.
Qed.

Print Assumptions guarded_replacement_image_equiv.
Print Assumptions bounded_replacement_derivable.
