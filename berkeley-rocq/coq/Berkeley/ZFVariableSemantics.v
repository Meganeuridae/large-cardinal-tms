(** Arbitrary bijective variable-name contexts for the ordinary Separation
    and Replacement schemata, at the model-theoretic level. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula FormulaSemantics FormulaRenaming NatPermutations LogicBridge LogicSemantics
  TheoryIrreflexiveND AugmentedLogic AugmentedSemantics ZFProtected.
Import ListNotations.
Lemma rename_separation pi p :
  rename_formula pi (conventional_separation p) =
  fill_template (separation_template (pi 0) (pi 1) (pi 2)) (rename_formula pi p).
Proof. reflexivity. Qed.
Lemma rename_replacement pi p :
  rename_formula pi (conventional_replacement p) =
  fill_template (replacement_template (pi 0) (pi 1) (pi 2) (pi 3)) (rename_formula pi p).
Proof. reflexivity. Qed.
Section RenamingModels.
Context {D:Type} (R:D->D->Prop).
Variable classic : forall P:Prop, P \/ ~P.
Hypothesis Model : satisfies_nonlogical_schemas R.
Theorem separation_in_arbitrary_variable_context pi sigma p :
  (forall n, sigma(pi n)=n) -> (forall n, pi(sigma n)=n) -> nd_free (pi 1) p=false ->
  forall rho, FolHolds R rho (fill_template (separation_template (pi 0) (pi 1) (pi 2)) p).
Proof.
  intros Left Right Free rho.
  assert (PI : forall a b, pi a=pi b -> a=b) by (intros a b E; apply (f_equal sigma) in E; now rewrite !Left in E).
  assert (SI : forall a b, sigma a=sigma b -> a=b) by (intros a b E; apply (f_equal pi) in E; now rewrite !Right in E).
  set (q:=rename_formula sigma p).
  assert (FreeQ : nd_free 1 q=false).
  { unfold q. pose proof (nd_free_rename sigma (pi 1) p SI) as H. rewrite Left,Free in H. exact H. }
  pose proof (augmented_sound_in_inhabited_model R classic Model (conventional_separation q)
    (conventional_separation_derivable q FreeQ) (fun n=>rho (pi n))) as H.
  apply (proj2 (FolHolds_rename R rho (conventional_separation q) pi PI)) in H.
  rewrite rename_separation in H. unfold q in H. now rewrite rename_inverse in H by exact Right.
Qed.
Theorem replacement_in_arbitrary_variable_context pi sigma p :
  (forall n, sigma(pi n)=n) -> (forall n, pi(sigma n)=n) -> nd_free (pi 1) p=false ->
  forall rho, FolHolds R rho (fill_template (replacement_template (pi 0) (pi 1) (pi 2) (pi 3)) p).
Proof.
  intros Left Right Free rho.
  assert (PI : forall a b, pi a=pi b -> a=b) by (intros a b E; apply (f_equal sigma) in E; now rewrite !Left in E).
  assert (SI : forall a b, sigma a=sigma b -> a=b) by (intros a b E; apply (f_equal pi) in E; now rewrite !Right in E).
  set (q:=rename_formula sigma p).
  assert (FreeQ : nd_free 1 q=false).
  { unfold q. pose proof (nd_free_rename sigma (pi 1) p SI) as H. rewrite Left,Free in H. exact H. }
  pose proof (augmented_sound_in_inhabited_model R classic Model (conventional_replacement q)
    (conventional_replacement_derivable q FreeQ) (fun n=>rho (pi n))) as H.
  apply (proj2 (FolHolds_rename R rho (conventional_replacement q) pi PI)) in H.
  rewrite rename_replacement in H. unfold q in H. now rewrite rename_inverse in H by exact Right.
Qed.
End RenamingModels.
Print Assumptions separation_in_arbitrary_variable_context.
Print Assumptions replacement_in_arbitrary_variable_context.

Section FiniteContexts.
Context {D:Type} (R:D->D->Prop).
Variable classic : forall P:Prop, P \/ ~P.
Hypothesis Model : satisfies_nonlogical_schemas R.
Theorem separation_for_distinct_variables x y z p : x<>y -> x<>z -> y<>z -> nd_free y p=false ->
  forall rho, FolHolds R rho (fill_template (separation_template x y z) p).
Proof.
  intros XY XZ YZ Free rho.
  set (w:=S (Nat.max x (Nat.max y z))).
  assert (XW:x<>w) by (unfold w;pose proof (Nat.le_max_l x (Nat.max y z));lia).
  assert (YW:y<>w) by (unfold w;pose proof (Nat.le_max_l y z);pose proof (Nat.le_max_r x (Nat.max y z));lia).
  assert (ZW:z<>w) by (unfold w;pose proof (Nat.le_max_r y z);pose proof (Nat.le_max_r x (Nat.max y z));lia).
  destruct (perm4_values x y z w XY XZ XW YZ YW ZW) as [P0 [P1 [P2 P3]]].
  pose proof (separation_in_arbitrary_variable_context R classic Model (perm4 x y z w) (invperm4 x y z w) p
    (perm4_left_inverse x y z w) (perm4_right_inverse x y z w)) as H.
  rewrite P1 in H. specialize (H Free rho). now rewrite P0,P2 in H.
Qed.
Theorem replacement_for_distinct_variables x y z w p :
  x<>y -> x<>z -> x<>w -> y<>z -> y<>w -> z<>w -> nd_free y p=false ->
  forall rho, FolHolds R rho (fill_template (replacement_template x y z w) p).
Proof.
  intros XY XZ XW YZ YW ZW Free rho.
  destruct (perm4_values x y z w XY XZ XW YZ YW ZW) as [P0 [P1 [P2 P3]]].
  pose proof (replacement_in_arbitrary_variable_context R classic Model (perm4 x y z w) (invperm4 x y z w) p
    (perm4_left_inverse x y z w) (perm4_right_inverse x y z w)) as H.
  rewrite P1 in H. specialize (H Free rho). now rewrite P0,P2,P3 in H.
Qed.
End FiniteContexts.
Print Assumptions separation_for_distinct_variables.
Print Assumptions replacement_for_distinct_variables.
