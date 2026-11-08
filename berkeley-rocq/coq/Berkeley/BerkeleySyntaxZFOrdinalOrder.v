(** Ordinal comparison from first-order Separation and Foundation. All
    membership and minimality statements range over internal objects. *)
From Stdlib Require Import Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxSets
  BerkeleySyntaxOmega BerkeleySyntaxCardinal BerkeleySyntaxZFBase
  BerkeleySyntaxZFSeparation BerkeleySyntaxZFFoundation BerkeleySyntaxZFOmegaOrder.

Section Comparison.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma zf_difference_exists a b : exists s, forall z, R z s <-> R z a /\ ~R z b.
Proof.
  set (rho := fun n:nat => if Nat.eqb n 0 then a else b).
  destruct (zf_prefix_formula_separation R EM Model (FNeg (FMember 2 3)) rho eq_refl) as [s S].
  exists s. exact S.
Qed.

Lemma subset_or_difference a b : RelSubset R a b \/ exists x, R x a /\ ~R x b.
Proof.
  destruct (EM (exists x, R x a /\ ~R x b)) as [E|N]; [now right|left].
  intros x X. destruct (EM (R x b)) as [B|B]; [exact B|].
  exfalso. apply N. now exists x.
Qed.

Lemma zf_least_difference a b : RelTransitive R a ->
  (exists x, R x a /\ ~R x b) ->
  exists x, R x a /\ ~R x b /\ RelSubset R x b.
Proof.
  intros Trans [x [X NX]]. destruct (zf_difference_exists a b) as [s S].
  assert (Nonempty : exists z, R z s) by (exists x; apply (proj2 (S x)); auto).
  destruct (zf_prefix_foundation R EM Model s Nonempty) as [y [Y Min]].
  destruct (proj1 (S y) Y) as [YA YB]. exists y. split; [exact YA|]. split; [exact YB|].
  intros z Z. destruct (EM (R z b)) as [B|B]; [exact B|].
  exfalso. apply (Min z Z). apply (proj2 (S z)). split; [exact (Trans y z YA Z)|exact B].
Qed.

Lemma zf_ordinal_subsets_comparable a b : RelOrdinal R a -> RelOrdinal R b ->
  RelSubset R a b \/ RelSubset R b a.
Proof.
  intros [TA LA] [TB LB]. destruct (subset_or_difference a b) as [AB|DA]; [now left|].
  destruct (subset_or_difference b a) as [BA|DB]; [now right|].
  destruct (zf_least_difference a b TA DA) as [x [XA [NX XB]]].
  destruct (zf_least_difference b a TB DB) as [y [YB [NY YA]]].
  assert (XY : RelSubset R x y).
  { intros u U. destruct (LB u y (XB u U) YB) as [[UY|UY]|YU]; [exact UY| |].
    - subst u. exfalso. exact (NY (TA x y XA U)).
    - exfalso. exact (NY (TA u y (TA x u XA U) YU)). }
  assert (YX : RelSubset R y x).
  { intros u U. destruct (LA u x (YA u U) XA) as [[UX|UX]|XU]; [exact UX| |].
    - subst u. exfalso. exact (NX (TB y x YB U)).
    - exfalso. exact (NX (TB u x (TB y u YB U) XU)). }
  assert (x=y) by (apply (zf_prefix_extensional R EM Model); intro u; split; [apply XY|apply YX]).
  subst y. contradiction.
Qed.

Lemma zf_ordinal_subset_cases a b : RelOrdinal R a -> RelOrdinal R b ->
  RelSubset R a b -> a=b \/ R a b.
Proof.
  intros [TA LA] [TB LB] AB. destruct (subset_or_difference b a) as [BA|Diff].
  - left. apply (zf_prefix_extensional R EM Model). intro z. split; [apply AB|apply BA].
  - destruct (zf_least_difference b a TB Diff) as [y [YB [NY YA]]].
    assert (AY : RelSubset R a y).
    { intros u U. destruct (LB u y (AB u U) YB) as [[UY|UY]|YU]; [exact UY| |].
      - subst u. contradiction.
      - exfalso. exact (NY (TA u y U YU)). }
    assert (a=y) by (apply (zf_prefix_extensional R EM Model); intro u; split; [apply AY|apply YA]).
    subst y. now right.
Qed.

Theorem zf_ordinal_comparison a b : RelOrdinal R a -> RelOrdinal R b ->
  (R a b \/ a=b) \/ R b a.
Proof.
  intros A B. destruct (zf_ordinal_subsets_comparable a b A B) as [AB|BA].
  - destruct (zf_ordinal_subset_cases a b A B AB); tauto.
  - destruct (zf_ordinal_subset_cases b a B A BA); [left; right; symmetry; assumption|now right].
Qed.

Theorem zf_internal_omega_linear w : RelOmega R w -> RelOrdinalLinear R w.
Proof.
  intros Omega a b A B. apply zf_ordinal_comparison.
  - exact (proj1 (zf_internal_natural_strong_ordinal R EM Model w Omega a A)).
  - exact (proj1 (zf_internal_natural_strong_ordinal R EM Model w Omega b B)).
Qed.

Theorem zf_internal_omega_ordinal w : RelOmega R w -> RelOrdinal R w.
Proof. intro Omega. split; [now apply (zf_internal_omega_transitive R EM Model)|now apply zf_internal_omega_linear]. Qed.
End Comparison.

Print Assumptions zf_difference_exists.
Print Assumptions zf_least_difference.
Print Assumptions zf_ordinal_comparison.
Print Assumptions zf_internal_omega_linear.
Print Assumptions zf_internal_omega_ordinal.
