(** First-order agreement formula for two fixed internal histories. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxZFSeparation BerkeleySyntaxZFStageAgreement BerkeleySyntaxZFStageLocal.
Import ListNotations.
Definition b_at_or_before n k := b_or (b_eq n k) (b_mem n k).
Definition b_local_core n h1 h2 a b := b_imp (b_rel h1 n a) (b_imp (b_rel h2 n b) (b_eq a b)).
Definition b_local_values n h1 h2 := b_all (fun a => b_all (fun b => b_local_core n h1 h2 a b)).
Definition b_local_agreement n k1 k2 h1 h2 :=
  b_imp (b_at_or_before n k1) (b_imp (b_at_or_before n k2) (b_local_values n h1 h2)).
Definition local_agreement_formula := instantiate_formula (fun _=>0) (fst (b_local_agreement 2 3 4 5 6 7)).
Lemma local_agreement_output_fresh : fol_free 1 local_agreement_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma b_good_at_or_before n k : b_good (b_at_or_before n k).
Proof. unfold b_at_or_before,b_or. apply b_good_binary; [apply b_good_eq|apply b_good_mem]. Qed.
Lemma b_good_local_core n h1 h2 a b : b_good (b_local_core n h1 h2 a b).
Proof.
  unfold b_local_core,b_imp. apply b_good_binary; [apply b_good_rel|].
  apply b_good_binary; [apply b_good_rel|apply b_good_eq].
Qed.
Lemma b_good_local_values n h1 h2 : b_good (b_local_values n h1 h2).
Proof. unfold b_local_values. do 2 (apply b_good_all;intro). apply b_good_local_core. Qed.
Section LocalFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Lemma at_or_before_holds rho n k start :
  b_holds R rho (b_at_or_before n k) start <-> RelAtOrBefore R (rho n) (rho k).
Proof.
  unfold b_at_or_before,RelAtOrBefore. rewrite (b_holds_or EM),b_holds_eq,b_holds_mem. reflexivity.
Qed.
Lemma local_core_holds rho n h1 h2 a b start : n<start -> h1<start -> h2<start -> a<start -> b<start ->
  (b_holds R rho (b_local_core n h1 h2 a b) start <->
   (RelGraph R (rho h1) (rho n) (rho a) -> RelGraph R (rho h2) (rho n) (rho b) -> rho a=rho b)).
Proof.
  intros N H1 H2 A B. unfold b_local_core. rewrite !b_holds_imp.
  assert (K1:start<=b_next (b_rel h1 n a) start) by apply b_good_rel.
  assert (K2:start<=b_next (b_rel h2 n b) (b_next (b_rel h1 n a) start)).
  { pose proof (b_good_rel h2 n b (b_next (b_rel h1 n a) start)). lia. }
  rewrite !(relation_builder_holds EM) by lia. rewrite b_holds_eq. reflexivity.
Qed.
Lemma local_values_holds rho n h1 h2 start : n<start -> h1<start -> h2<start ->
  (b_holds R rho (b_local_values n h1 h2) start <->
   forall a b, RelGraph R (rho h1) (rho n) a -> RelGraph R (rho h2) (rho n) b -> a=b).
Proof.
  intros N H1 H2. unfold b_local_values. rewrite b_holds_all. split.
  - intros T a. specialize (T a). rewrite b_holds_all in T. intros b. specialize (T b).
    rewrite local_core_holds in T by lia.
    set (sigma:=update_variable (update_variable rho start a) (S start) b) in T.
    assert (Sn:sigma n=rho n) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (S1:sigma h1=rho h1) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (S2:sigma h2=rho h2) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma start=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S start)=b) by (unfold sigma;apply update_variable_eq).
    now rewrite Sn,S1,S2,Sa,Sb in T.
  - intros T a. rewrite b_holds_all. intros b. rewrite local_core_holds by lia.
    set (sigma:=update_variable (update_variable rho start a) (S start) b).
    change (RelGraph R (sigma h1) (sigma n) (sigma start) ->
      RelGraph R (sigma h2) (sigma n) (sigma (S start)) -> sigma start=sigma (S start)).
    assert (Sn:sigma n=rho n) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (S1:sigma h1=rho h1) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (S2:sigma h2=rho h2) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma start=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S start)=b) by (unfold sigma;apply update_variable_eq).
    rewrite Sn,S1,S2,Sa,Sb. now apply T.
Qed.
Theorem local_agreement_formula_holds rho : FolHolds R rho local_agreement_formula <->
  RelLocalAgreement R (rho 5) (rho 6) (rho 3) (rho 4) (rho 2).
Proof.
  change (b_holds R rho (b_local_agreement 2 3 4 5 6) 7 <->
    RelLocalAgreement R (rho 5) (rho 6) (rho 3) (rho 4) (rho 2)).
  unfold b_local_agreement,RelLocalAgreement. rewrite !b_holds_imp.
  assert (K1:7<=b_next (b_at_or_before 2 3) 7) by apply b_good_at_or_before.
  assert (K2:7<=b_next (b_at_or_before 2 4) (b_next (b_at_or_before 2 3) 7)).
  { pose proof (b_good_at_or_before 2 4 (b_next (b_at_or_before 2 3) 7)). lia. }
  rewrite !at_or_before_holds,local_values_holds by lia. reflexivity.
Qed.
End LocalFormula.
Print Assumptions local_agreement_output_fresh.
Print Assumptions local_agreement_formula_holds.
