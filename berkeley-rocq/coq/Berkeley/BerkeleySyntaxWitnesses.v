(** Interpretation of fixed points, critical points, and cofinal witnesses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntax BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxElementary FormulaSemantics.
Import ListNotations.

Definition fixed_builder j k := b_ain k (fun a => b_rel j a a).
Definition RelFixedBelow {D} (R:D->D->Prop) j k := forall a, R a k -> RelGraph R j a a.
Definition RelCritical {D} (R:D->D->Prop) j k d eta :=
  R k d /\ R eta k /\ ~RelGraph R j k k /\ RelFixedBelow R j k.
Definition RelBerkeleyWitnesses {D} (R:D->D->Prop) d m e f w sat :=
  forall eta, R eta d -> exists j k, RelCritical R j k d eta /\ RelElementary R j m e f w sat.

Lemma b_good_fixed j k : b_good (fixed_builder j k).
Proof. unfold fixed_builder. apply b_good_ain. intro a. apply b_good_rel. Qed.
Lemma b_good_critical j k d eta : b_good (b_critical j k d eta).
Proof.
  unfold b_critical,b_and4,b_and3. repeat apply b_good_and;
    try apply b_good_mem; try (apply b_good_not,b_good_rel); apply b_good_fixed.
Qed.

Section WitnessSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma fixed_builder_holds rho j k n : j<n -> k<n ->
  (b_holds R rho (fixed_builder j k) n <-> RelFixedBelow R (rho j) (rho k)).
Proof.
  intros J K. unfold fixed_builder,RelFixedBelow. rewrite b_holds_ain by exact K. split; intros H a A; specialize (H a A).
  - rewrite (relation_builder_holds EM) in H by lia. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite (relation_builder_holds EM) by lia. rewrite update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.

Theorem critical_builder_holds rho j k d eta n : j<n -> k<n -> d<n -> eta<n ->
  (b_holds R rho (b_critical j k d eta) n <-> RelCritical R (rho j) (rho k) (rho d) (rho eta)).
Proof.
  intros J K D0 E. unfold b_critical,RelCritical,b_and4,b_and3.
  change (b_holds R rho (b_and (b_and (b_and (b_mem k d) (b_mem eta k)) (b_not (b_rel j k k))) (fixed_builder j k)) n <->
    R (rho k) (rho d) /\ R (rho eta) (rho k) /\ ~RelGraph R (rho j) (rho k) (rho k) /\ RelFixedBelow R (rho j) (rho k)).
  rewrite !(b_holds_and EM),!b_holds_mem,b_holds_not.
  assert (K1 : n <= b_next (b_and (b_mem k d) (b_mem eta k)) n) by (apply b_good_and; apply b_good_mem).
  assert (K2 : n <= b_next (b_and (b_and (b_mem k d) (b_mem eta k)) (b_not (b_rel j k k))) n)
    by (repeat apply b_good_and; try apply b_good_mem; apply b_good_not,b_good_rel).
  rewrite (relation_builder_holds EM),fixed_builder_holds by lia. tauto.
Qed.

Theorem witnesses_builder_holds rho d m e f w sat n :
  d<n -> m<n -> e<n -> f<n -> w<n -> sat<n ->
  (b_holds R rho (b_berkeley_witnesses d m e f w sat) n <->
   RelBerkeleyWitnesses R (rho d) (rho m) (rho e) (rho f) (rho w) (rho sat)).
Proof.
  intros D0 M E F W Sat. unfold b_berkeley_witnesses,RelBerkeleyWitnesses. rewrite b_holds_ain by exact D0.
  split; intros H eta Eta; specialize (H eta Eta).
  - rewrite (b_holds_ex EM) in H. destruct H as [j H]. rewrite (b_holds_ex EM) in H. destruct H as [k H]. rewrite (b_holds_and EM) in H.
    assert (K : S(S(S n)) <= b_next (b_critical (S n) (S(S n)) d n) (S(S(S n))) ) by apply b_good_critical.
    rewrite critical_builder_holds,(elementary_builder_holds EM) in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n eta) (S n) j) (S(S n)) k) in H.
    assert (Sd : sigma d=rho d) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Seta : sigma n=eta) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sj : sigma (S n)=j) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sk : sigma (S(S n))=k) by (unfold sigma; apply update_variable_eq).
    rewrite Sd,Sm,Se,Sf,Sw,Ss,Seta,Sj,Sk in H. now exists j,k.
  - destruct H as [j [k H]]. rewrite (b_holds_ex EM). exists j. rewrite (b_holds_ex EM). exists k. rewrite (b_holds_and EM).
    assert (K : S(S(S n)) <= b_next (b_critical (S n) (S(S n)) d n) (S(S(S n))) ) by apply b_good_critical.
    rewrite critical_builder_holds,(elementary_builder_holds EM) by lia.
    set (sigma := update_variable (update_variable (update_variable rho n eta) (S n) j) (S(S n)) k).
    change (RelCritical R (sigma (S n)) (sigma (S(S n))) (sigma d) (sigma n) /\
      RelElementary R (sigma (S n)) (sigma m) (sigma e) (sigma f) (sigma w) (sigma sat)).
    assert (Sd : sigma d=rho d) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Seta : sigma n=eta) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sj : sigma (S n)=j) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sk : sigma (S(S n))=k) by (unfold sigma; apply update_variable_eq).
    now rewrite Sd,Sm,Se,Sf,Sw,Ss,Seta,Sj,Sk.
Qed.
End WitnessSemantics.

Print Assumptions fixed_builder_holds.
Print Assumptions critical_builder_holds.
Print Assumptions witnesses_builder_holds.
