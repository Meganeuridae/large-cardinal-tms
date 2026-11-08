(** The protected formula in source Separation and Replacement is equivalent
    to the ordinary fresh-output formula, for arbitrary variable names and
    arbitrary formula parameters. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofPresentation LogicBridge LogicFresh
  TheoryIrreflexiveND AugmentedLogic AugmentedInstantiation StandardND StandardAugEquivalence.
Import ListNotations.
Definition AugEquiv p q := AugProvable (FImp p q) /\ AugProvable (FImp q p).
Lemma aug_equiv_refl p : AugEquiv p p.
Proof. split; apply aug_logical,logical_identity. Qed.
Lemma aug_weaken_theorem p e : AugProvable p -> AugProvable (FImp e p).
Proof. intro H. eapply aug_mp; [apply aug_logical,logical_b1|exact H]. Qed.
Lemma aug_truth : AugProvable nd_true.
Proof. unfold nd_true. apply aug_logical,logical_identity. Qed.
Lemma aug_equiv_neg p q : AugEquiv p q -> AugEquiv (FNeg p) (FNeg q).
Proof.
  intros [F B]. destruct (aug_inst_neg_substitution nd_true p q
    (aug_weaken_theorem _ _ F) (aug_weaken_theorem _ _ B)) as [H K].
  split; eapply aug_mp; [exact H|apply aug_truth|exact K|apply aug_truth].
Qed.
Lemma aug_equiv_imp p p' q q' : AugEquiv p p' -> AugEquiv q q' -> AugEquiv (FImp p q) (FImp p' q').
Proof.
  intros [PF PB] [QF QB]. destruct (aug_inst_imp_substitution nd_true p p' q q'
    (aug_weaken_theorem _ _ PF) (aug_weaken_theorem _ _ PB)
    (aug_weaken_theorem _ _ QF) (aug_weaken_theorem _ _ QB)) as [H K].
  split; eapply aug_mp; [exact H|apply aug_truth|exact K|apply aug_truth].
Qed.
Lemma aug_equiv_all x p q : AugEquiv p q -> AugEquiv (FAll x p) (FAll x q).
Proof. intros [F B]. split; now apply aug_all_monotone. Qed.
Lemma aug_instance_congruence f vars holes holes' :
  (forall n, AugEquiv (holes n) (holes' n)) ->
  AugEquiv (independent_instance vars holes f) (independent_instance vars holes' f).
Proof.
  intro Eq. induction f as [b x y|p IH|p IH q JH|x p IH|n]; cbn [independent_instance].
  - destruct b; apply aug_equiv_refl.
  - now apply aug_equiv_neg.
  - now apply aug_equiv_imp.
  - now apply aug_equiv_all.
  - apply Eq.
Qed.
Definition fill_template f p := independent_instance (fun n=>n) (fun _=>p) f.
Definition separation_template x y z :=
  let x:=V x in let y:=V y in let z:=V z in
  SEx y (All z (SIff (SMember z y) (SAnd (SMember z x) (Hole 1)))).
Definition replacement_template x y z w :=
  let x:=V x in let y:=V y in let z:=V z in let w:=V w in
  Imp (All w (SEx y (All z (Imp (Hole 1) (SEqual z y)))))
      (SEx y (All z (SIff (SMember z y) (SEx w (SAnd (SMember w x) (Hole 1)))))).
Lemma aug_protection_equiv y p : nd_free y p=false -> AugEquiv (FAll y p) p.
Proof.
  intro F. split; [apply aug_logical,logical_b5|apply aug_fresh_C5,nd_free_not_occurs,F].
Qed.
Theorem separation_protected_equiv x y z p : nd_free y p=false ->
  AugEquiv (fill_template (separation_template x y z) (FAll y p))
           (fill_template (separation_template x y z) p).
Proof. intro F. apply aug_instance_congruence. intro n. now apply aug_protection_equiv. Qed.
Theorem replacement_protected_equiv x y z w p : nd_free y p=false ->
  AugEquiv (fill_template (replacement_template x y z w) (FAll y p))
           (fill_template (replacement_template x y z w) p).
Proof. intro F. apply aug_instance_congruence. intro n. now apply aug_protection_equiv. Qed.
Definition conventional_separation p := fill_template (separation_template 0 1 2) p.
Definition conventional_replacement p := fill_template (replacement_template 0 1 2 3) p.
Lemma source_separation_instance p : AugProvable (conventional_separation (FAll 1 p)).
Proof.
  change (AugProvable (independent_instance (fun n=>n) (fun _=>p) (nth 20 candidate_axioms (Hole 0)))).
  apply aug_original. eapply presented_axiom with (i:=20). reflexivity.
Qed.
Lemma source_replacement_instance p : AugProvable (conventional_replacement (FAll 1 p)).
Proof.
  change (AugProvable (independent_instance (fun n=>n) (fun _=>p) (nth 21 candidate_axioms (Hole 0)))).
  apply aug_original. eapply presented_axiom with (i:=21). reflexivity.
Qed.
Theorem conventional_separation_derivable p : nd_free 1 p=false -> AugProvable (conventional_separation p).
Proof.
  intro F. eapply aug_mp; [apply (proj1 (separation_protected_equiv 0 1 2 p F))|apply source_separation_instance].
Qed.
Theorem conventional_replacement_derivable p : nd_free 1 p=false -> AugProvable (conventional_replacement p).
Proof.
  intro F. eapply aug_mp; [apply (proj1 (replacement_protected_equiv 0 1 2 3 p F))|apply source_replacement_instance].
Qed.
Print Assumptions aug_instance_congruence.
Print Assumptions separation_protected_equiv.
Print Assumptions replacement_protected_equiv.
Print Assumptions conventional_separation_derivable.
Print Assumptions conventional_replacement_derivable.
