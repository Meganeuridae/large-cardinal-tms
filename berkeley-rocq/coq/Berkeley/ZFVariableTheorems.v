(** Ordinary Separation and Replacement instances in any distinct finite
    variable context are theorems of the normalized repaired calculus. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Berkeley Require Import Syntax TheorySchemas ProofFormula LogicBridge FormulaRenaming NatPermutations
  TheoryIrreflexiveND AugmentedLogic StandardND StandardAugEquivalence ZFProtected
  ZFVariableSemantics StandardPermutation ZFConventionalND.
Import ListNotations.

Theorem standard_separation_perm4 x y z w p :
  nd_free (perm4 x y z w 1) p=false ->
  StandardND [] (fill_template (separation_template (perm4 x y z w 0)
    (perm4 x y z w 1) (perm4 x y z w 2)) p).
Proof.
  intro Free. set (pi:=perm4 x y z w). set (sigma:=invperm4 x y z w).
  change (nd_free (pi 1) p=false) in Free.
  assert (Left : forall n, sigma (pi n)=n) by apply perm4_left_inverse.
  assert (Right : forall n, pi (sigma n)=n) by apply perm4_right_inverse.
  assert (SI : forall a b, sigma a=sigma b -> a=b).
  { intros a b E. apply (f_equal pi) in E. now rewrite !Right in E. }
  set (q:=rename_formula sigma p).
  assert (FreeQ : nd_free 1 q=false).
  { unfold q. pose proof (nd_free_rename sigma (pi 1) p SI) as H. rewrite Left,Free in H. exact H. }
  pose proof (standard_theorem_perm4 x y z w (conventional_separation q)
    (augmented_theorem_to_standard _ (conventional_separation_derivable q FreeQ))) as H.
  change (StandardND [] (rename_formula pi (conventional_separation q))) in H.
  rewrite rename_separation in H. unfold q in H. now rewrite rename_inverse in H by exact Right.
Qed.

Theorem standard_replacement_perm4 x y z w p :
  nd_free (perm4 x y z w 1) p=false ->
  StandardND [] (fill_template (replacement_template (perm4 x y z w 0)
    (perm4 x y z w 1) (perm4 x y z w 2) (perm4 x y z w 3)) p).
Proof.
  intro Free. set (pi:=perm4 x y z w). set (sigma:=invperm4 x y z w).
  change (nd_free (pi 1) p=false) in Free.
  assert (Left : forall n, sigma (pi n)=n) by apply perm4_left_inverse.
  assert (Right : forall n, pi (sigma n)=n) by apply perm4_right_inverse.
  assert (SI : forall a b, sigma a=sigma b -> a=b).
  { intros a b E. apply (f_equal pi) in E. now rewrite !Right in E. }
  set (q:=rename_formula sigma p).
  assert (FreeQ : nd_free 1 q=false).
  { unfold q. pose proof (nd_free_rename sigma (pi 1) p SI) as H. rewrite Left,Free in H. exact H. }
  pose proof (standard_theorem_perm4 x y z w (conventional_replacement q)
    (augmented_theorem_to_standard _ (conventional_replacement_derivable q FreeQ))) as H.
  change (StandardND [] (rename_formula pi (conventional_replacement q))) in H.
  rewrite rename_replacement in H. unfold q in H. now rewrite rename_inverse in H by exact Right.
Qed.

Theorem standard_separation_distinct x y z p :
  x<>y -> x<>z -> y<>z -> nd_free y p=false ->
  StandardND [] (fill_template (separation_template x y z) p).
Proof.
  intros XY XZ YZ Free. set (w:=S (Nat.max x (Nat.max y z))).
  assert (XW:x<>w) by (unfold w;pose proof (Nat.le_max_l x (Nat.max y z));lia).
  assert (YW:y<>w) by (unfold w;pose proof (Nat.le_max_l y z);pose proof (Nat.le_max_r x (Nat.max y z));lia).
  assert (ZW:z<>w) by (unfold w;pose proof (Nat.le_max_r y z);pose proof (Nat.le_max_r x (Nat.max y z));lia).
  destruct (perm4_values x y z w XY XZ XW YZ YW ZW) as [P0 [P1 [P2 P3]]].
  pose proof (standard_separation_perm4 x y z w p) as H.
  rewrite P0,P1,P2 in H. exact (H Free).
Qed.

Theorem standard_replacement_distinct x y z w p :
  x<>y -> x<>z -> x<>w -> y<>z -> y<>w -> z<>w -> nd_free y p=false ->
  StandardND [] (fill_template (replacement_template x y z w) p).
Proof.
  intros XY XZ XW YZ YW ZW Free.
  destruct (perm4_values x y z w XY XZ XW YZ YW ZW) as [P0 [P1 [P2 P3]]].
  pose proof (standard_replacement_perm4 x y z w p) as H.
  rewrite P0,P1,P2,P3 in H. exact (H Free).
Qed.
Theorem conventional_separation_distinct x y z p :
  x<>y -> x<>z -> y<>z -> nd_free y p=false ->
  ConventionalND [] (fill_template (separation_template x y z) p).
Proof. intros. apply standard_to_conventional,standard_separation_distinct; assumption. Qed.

Theorem conventional_replacement_distinct x y z w p :
  x<>y -> x<>z -> x<>w -> y<>z -> y<>w -> z<>w -> nd_free y p=false ->
  ConventionalND [] (fill_template (replacement_template x y z w) p).
Proof. intros. apply standard_to_conventional,standard_replacement_distinct; assumption. Qed.
Print Assumptions conventional_separation_distinct.
Print Assumptions conventional_replacement_distinct.
Print Assumptions standard_separation_distinct.
Print Assumptions standard_replacement_distinct.
