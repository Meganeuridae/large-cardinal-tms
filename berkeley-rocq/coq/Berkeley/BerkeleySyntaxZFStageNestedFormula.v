(** First-order induction predicate for monotonicity of a fixed stage history. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxZFSeparation BerkeleySyntaxZFPairStage
  BerkeleySyntaxZFStageAgreement BerkeleySyntaxZFStageLocalFormula BerkeleySyntaxZFStageNested.
Import ListNotations.
Definition b_nested_core n h i a b := b_imp (b_rel h i a) (b_imp (b_rel h n b) (b_subset a b)).
Definition b_nested_values n h i := b_all (fun a=>b_all (fun b=>b_nested_core n h i a b)).
Definition b_nested_at n k h := b_imp (b_at_or_before n k) (b_ain n (fun i=>b_nested_values n h i)).
Definition nested_at_formula := instantiate_formula (fun _=>0) (fst (b_nested_at 2 3 4 5)).
Lemma nested_at_output_fresh : fol_free 1 nested_at_formula=false.
Proof. vm_compute. reflexivity. Qed.
Section NestedFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Lemma nested_core_holds rho n h i a b start : n<start -> h<start -> i<start -> a<start -> b<start ->
  (b_holds R rho (b_nested_core n h i a b) start <->
   (RelGraph R (rho h) (rho i) (rho a) -> RelGraph R (rho h) (rho n) (rho b) -> RelSubset R (rho a) (rho b))).
Proof.
  intros N H I A B. unfold b_nested_core. rewrite !b_holds_imp.
  assert (K1:start<=b_next (b_rel h i a) start) by apply b_good_rel.
  assert (K2:start<=b_next (b_rel h n b) (b_next (b_rel h i a) start)).
  { pose proof (b_good_rel h n b (b_next (b_rel h i a) start)). lia. }
  rewrite !(relation_builder_holds EM),subset_builder_holds by lia. reflexivity.
Qed.
Lemma nested_values_holds rho n h i start : n<start -> h<start -> i<start ->
  (b_holds R rho (b_nested_values n h i) start <->
   forall a b, RelGraph R (rho h) (rho i) a -> RelGraph R (rho h) (rho n) b -> RelSubset R a b).
Proof.
  intros N H I. unfold b_nested_values. rewrite b_holds_all. split.
  - intros T a. specialize (T a). rewrite b_holds_all in T. intros b. specialize (T b).
    rewrite nested_core_holds in T by lia.
    set (sigma:=update_variable (update_variable rho start a) (S start) b) in T.
    assert (Sn:sigma n=rho n) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma i=rho i) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma start=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S start)=b) by (unfold sigma;apply update_variable_eq).
    now rewrite Sn,Sh,Si,Sa,Sb in T.
  - intros T a. rewrite b_holds_all. intros b. rewrite nested_core_holds by lia.
    set (sigma:=update_variable (update_variable rho start a) (S start) b).
    change (RelGraph R (sigma h) (sigma i) (sigma start) ->
      RelGraph R (sigma h) (sigma n) (sigma (S start)) -> RelSubset R (sigma start) (sigma (S start))).
    assert (Sn:sigma n=rho n) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma i=rho i) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma start=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S start)=b) by (unfold sigma;apply update_variable_eq).
    rewrite Sn,Sh,Si,Sa,Sb. now apply T.
Qed.
Theorem nested_at_formula_holds rho : FolHolds R rho nested_at_formula <->
  RelNestedAt R (rho 4) (rho 3) (rho 2).
Proof.
  change (b_holds R rho (b_nested_at 2 3 4) 5 <-> RelNestedAt R (rho 4) (rho 3) (rho 2)).
  unfold b_nested_at,RelNestedAt. rewrite b_holds_imp,(at_or_before_holds R EM).
  replace (b_next (b_at_or_before 2 3) 5) with 5 by reflexivity.
  rewrite b_holds_ain by lia. setoid_rewrite nested_values_holds; try lia.
  cbv [update_variable Nat.eqb]. split.
  - intros H Before i a b I. now apply (H Before i I a b).
  - intros H Before i I a b. now apply (H Before i a b I).
Qed.
End NestedFormula.
Print Assumptions nested_at_output_fresh.
Print Assumptions nested_at_formula_holds.
