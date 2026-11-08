(** First-order graph-composition relation for a Replacement instance. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition composition_core_builder z input s j mid y :=
  b_and3 (b_rel s input mid) (b_rel j mid y) (b_pair z input y).
Definition composition_inner_builder z input s j := b_ex (fun mid => b_ex (fun y =>
  composition_core_builder z input s j mid y)).
Definition composition_formula_builder := b_and (b_mem 3 6) (composition_inner_builder 2 3 4 5).
Definition composition_formula := instantiate_formula (fun _=>0) (fst (composition_formula_builder 7)).
Lemma composition_formula_output_fresh : fol_free 1 composition_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section CompositionFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma composition_core_holds rho z input s j mid y n :
  z<n -> input<n -> s<n -> j<n -> mid<n -> y<n ->
  (b_holds R rho (composition_core_builder z input s j mid y) n <->
    RelGraph R (rho s) (rho input) (rho mid) /\
    RelGraph R (rho j) (rho mid) (rho y) /\ RelPair R (rho z) (rho input) (rho y)).
Proof.
  intros Z I S0 J M Y. unfold composition_core_builder,b_and3. rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (b_rel s input mid) n) by apply b_good_rel.
  assert (K2 : n <= b_next (b_and (b_rel s input mid) (b_rel j mid y)) n)
    by (apply b_good_and; apply b_good_rel).
  rewrite !(relation_builder_holds EM),(pair_builder_holds EM) by lia. tauto.
Qed.

Lemma composition_inner_holds rho z input s j n : z<n -> input<n -> s<n -> j<n ->
  (b_holds R rho (composition_inner_builder z input s j) n <-> exists mid y,
    RelGraph R (rho s) (rho input) mid /\ RelGraph R (rho j) mid y /\ RelPair R (rho z) (rho input) y).
Proof.
  intros Z I S0 J. unfold composition_inner_builder. rewrite (b_holds_ex EM). split.
  - intros [mid H]. rewrite (b_holds_ex EM) in H. destruct H as [y H]. rewrite composition_core_holds in H by lia.
    set (sigma := update_variable (update_variable rho n mid) (S n) y) in H.
    assert (Sz : sigma z=rho z) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Si : sigma input=rho input) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma n=mid) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sz,Si,Ss,Sj,Sm,Sy in H. now exists mid,y.
  - intros [mid [y H]]. exists mid. rewrite (b_holds_ex EM). exists y. rewrite composition_core_holds by lia.
    set (sigma := update_variable (update_variable rho n mid) (S n) y).
    change (RelGraph R (sigma s) (sigma input) (sigma n) /\ RelGraph R (sigma j) (sigma n) (sigma (S n)) /\
      RelPair R (sigma z) (sigma input) (sigma (S n))).
    assert (Sz : sigma z=rho z) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Si : sigma input=rho input) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma n=mid) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    now rewrite Sz,Si,Ss,Sj,Sm,Sy.
Qed.

Theorem composition_formula_holds rho : FolHolds R rho composition_formula <->
  R (rho 3) (rho 6) /\ exists mid y, RelGraph R (rho 4) (rho 3) mid /\
    RelGraph R (rho 5) mid y /\ RelPair R (rho 2) (rho 3) y.
Proof.
  change (b_holds R rho composition_formula_builder 7 <->
    R (rho 3) (rho 6) /\ exists mid y, RelGraph R (rho 4) (rho 3) mid /\
      RelGraph R (rho 5) mid y /\ RelPair R (rho 2) (rho 3) y).
  unfold composition_formula_builder. rewrite (b_holds_and EM),b_holds_mem.
  replace (b_next (b_mem 3 6) 7) with 7 by reflexivity. rewrite composition_inner_holds by lia. reflexivity.
Qed.
End CompositionFormula.

Print Assumptions composition_formula_output_fresh.
Print Assumptions composition_formula_holds.
