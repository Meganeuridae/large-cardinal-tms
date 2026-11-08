(** Any two literal Tarski truth sets agree on every internal formula and
    environment. The induction predicate is an explicit first-order formula;
    no external well-foundedness of internal syntax is assumed. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment BerkeleySyntaxSatisfactionAtomic
  BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation BerkeleySyntaxFormulaInduction.
Import ListNotations.

Definition agreement_builder p e sat1 sat2 :=
  b_ain e (fun s => b_iff (b_rel sat1 p s) (b_rel sat2 p s)).
Definition RelSatisfactionAgreement {D} (R:D->D->Prop) p e sat1 sat2 :=
  forall s, R s e -> (RelGraph R sat1 p s <-> RelGraph R sat2 p s).
Definition agreement_formula := instantiate_formula (fun _=>0) (fst (agreement_builder 2 3 4 5 6)).
Lemma agreement_output_fresh : fol_free 1 agreement_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section AgreementSemantics.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma agreement_builder_holds rho p e sat1 sat2 n : p<n -> e<n -> sat1<n -> sat2<n ->
  (b_holds R rho (agreement_builder p e sat1 sat2) n <->
   RelSatisfactionAgreement R (rho p) (rho e) (rho sat1) (rho sat2)).
Proof.
  intros P E S1 S2. unfold agreement_builder,RelSatisfactionAgreement. rewrite b_holds_ain by exact E.
  split; intros H s Sin; specialize (H s Sin).
  - rewrite (b_holds_iff EM) in H.
    assert (K : S n <= b_next (b_rel sat1 p n) (S n)) by apply b_good_rel.
    rewrite !(relation_builder_holds EM) in H by lia. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite (b_holds_iff EM).
    assert (K : S n <= b_next (b_rel sat1 p n) (S n)) by apply b_good_rel.
    rewrite !(relation_builder_holds EM) by lia. rewrite update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.
Theorem agreement_formula_holds rho : FolHolds R rho agreement_formula <->
  RelSatisfactionAgreement R (rho 2) (rho 3) (rho 4) (rho 5).
Proof.
  change (b_holds R rho (agreement_builder 2 3 4 5) 6 <->
    RelSatisfactionAgreement R (rho 2) (rho 3) (rho 4) (rho 5)).
  rewrite agreement_builder_holds by lia. reflexivity.
Qed.
End AgreementSemantics.

Section TruthUniqueness.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_internal_satisfaction_unique f w m e te tm tn ti ta sat1 sat2 :
  RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  RelSatisfaction R sat1 e f w m te tm tn ti ta -> RelSatisfaction R sat2 e f w m te tm tn ti ta ->
  forall p s, R p f -> R s e -> (RelGraph R sat1 p s <-> RelGraph R sat2 p s).
Proof.
  intros Formulas Env Sat1 Sat2.
  set (rho := update_variable (update_variable (update_variable (fun _ : nat => f) 3 e) 4 sat1) 5 sat2).
  assert (Interpret : forall p, RelFormulaProperty R agreement_formula rho p <-> RelSatisfactionAgreement R p e sat1 sat2).
  { intro p. unfold RelFormulaProperty. rewrite (agreement_formula_holds R EM). unfold rho.
    cbv [update_variable Nat.eqb]. reflexivity. }
  assert (AllAgreement : forall p, R p f -> RelFormulaProperty R agreement_formula rho p).
  { eapply (zf_internal_formula_induction R EM Model f w te tm tn ti ta agreement_formula rho);
      [reflexivity|exact agreement_output_fresh|exact Formulas| | | | |].
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)). intros s S.
      destruct (proj1 (Env s) S) as [_ Total]. destruct (Total x X) as [a [A [Ga _]]].
      destruct (Total y Y) as [b [B [Gb _]]].
      destruct (Sat1 s S) as [Eq1 _]. destruct (Sat2 s S) as [Eq2 _].
      specialize (Eq1 x y a b p X Y A B Ga Gb Node). specialize (Eq2 x y a b p X Y A B Ga Gb Node).
      cbn [atom_truth] in Eq1,Eq2. tauto.
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)). intros s S.
      destruct (proj1 (Env s) S) as [_ Total]. destruct (Total x X) as [a [A [Ga _]]].
      destruct (Total y Y) as [b [B [Gb _]]].
      destruct (Sat1 s S) as [_ [Mem1 _]]. destruct (Sat2 s S) as [_ [Mem2 _]].
      specialize (Mem1 x y a b p X Y A B Ga Gb Node). specialize (Mem2 x y a b p X Y A B Ga Gb Node).
      cbn [atom_truth] in Mem1,Mem2. tauto.
    - intros q p Qf Qp Pf Pair. apply (proj2 (Interpret p)). intros s S.
      pose proof (proj1 (Interpret q) Qp s S) as IH.
      destruct (Sat1 s S) as [_ [_ [N1 _]]]. destruct (Sat2 s S) as [_ [_ [N2 _]]].
      specialize (N1 q p Qf Pair). specialize (N2 q p Qf Pair). tauto.
    - intros q r p Qf Qp Rf Rp Pf Node. apply (proj2 (Interpret p)). intros s S.
      pose proof (proj1 (Interpret q) Qp s S) as IH1. pose proof (proj1 (Interpret r) Rp s S) as IH2.
      destruct (Sat1 s S) as [_ [_ [_ [I1 _]]]]. destruct (Sat2 s S) as [_ [_ [_ [I2 _]]]].
      specialize (I1 q r p Qf Rf Node). specialize (I2 q r p Qf Rf Node). tauto.
    - intros x q p X Qf Qp Pf Node. apply (proj2 (Interpret p)). intros s S.
      pose proof (proj1 (Interpret q) Qp) as IH.
      destruct (Sat1 s S) as [_ [_ [_ [_ A1]]]]. destruct (Sat2 s S) as [_ [_ [_ [_ A2]]]].
      specialize (A1 x q p X Qf Node). specialize (A2 x q p X Qf Node).
      rewrite A1,A2. split; intros H t T Up; [apply (proj1 (IH t T))|apply (proj2 (IH t T))]; now apply H. }
  intros p s P S. exact ((proj1 (Interpret p)) (AllAgreement p P) s S).
Qed.
End TruthUniqueness.

Print Assumptions agreement_formula_holds.
Print Assumptions zf_internal_satisfaction_unique.
