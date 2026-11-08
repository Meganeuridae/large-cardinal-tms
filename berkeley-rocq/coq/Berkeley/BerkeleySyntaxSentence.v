(** Relational interpretation of the entire reconstructed finite sentence.
    These definitions describe its literal set-sized truth apparatus; they do
    not assert that such an apparatus exists or identify it with ZF semantics. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxSatisfaction BerkeleySyntax BerkeleySyntaxInterpretation BerkeleySyntaxSets BerkeleySyntaxOmega
  BerkeleySyntaxFormulaSet BerkeleySyntaxCardinalWitness BerkeleySyntaxScope BerkeleySyntaxBridge BerkeleyAlpha.
Import ListNotations.

Definition b_tags0 w z0 := b_and (b_omega w) (b_empty z0).
Definition b_tags1 w z0 z1 := b_and (b_tags0 w z0) (b_successor z1 z0).
Definition b_tags2 w z0 z1 z2 := b_and (b_tags1 w z0 z1) (b_successor z2 z1).
Definition b_tags3 w z0 z1 z2 z3 := b_and (b_tags2 w z0 z1 z2) (b_successor z3 z2).
Definition b_tags4 w z0 z1 z2 z3 z4 := b_and (b_tags3 w z0 z1 z2 z3) (b_successor z4 z3).
Definition b_sentence_setup w z0 z1 z2 z3 z4 f :=
  b_and (b_tags4 w z0 z1 z2 z3 z4) (b_formulas f w z0 z1 z2 z3 z4).
Definition b_sentence_body w z0 z1 z2 z3 z4 f :=
  b_and (b_sentence_setup w z0 z1 z2 z3 z4 f) (b_berkeley_cardinal f w z0 z1 z2 z3 z4).

Definition RelTags {D} (R:D->D->Prop) w z0 z1 z2 z3 z4 :=
  RelOmega R w /\ RelEmpty R z0 /\ RelSuccessor R z1 z0 /\ RelSuccessor R z2 z1 /\
  RelSuccessor R z3 z2 /\ RelSuccessor R z4 z3.
Definition RelSentenceSetup {D} (R:D->D->Prop) w z0 z1 z2 z3 z4 f :=
  RelTags R w z0 z1 z2 z3 z4 /\ RelFormulas R f w z0 z1 z2 z3 z4.
Definition RelSentenceBody {D} (R:D->D->Prop) w z0 z1 z2 z3 z4 f :=
  RelSentenceSetup R w z0 z1 z2 z3 z4 f /\ RelBerkeleyCardinal R f w z0 z1 z2 z3 z4.
Definition RelBerkeleySentence {D} (R:D->D->Prop) :=
  exists w z0 z1 z2 z3 z4 f, RelSentenceBody R w z0 z1 z2 z3 z4 f.

Lemma b_good_subset a b : b_good (b_subset a b).
Proof. unfold b_subset. apply b_good_ain. intro x. apply b_good_mem. Qed.
Lemma b_good_omega w : b_good (b_omega w).
Proof.
  unfold b_omega. apply b_good_and; [apply b_good_inductive|]. apply b_good_all. intro a.
  unfold b_imp. apply b_good_binary; [apply b_good_inductive|apply b_good_subset].
Qed.
Lemma b_good_formulas f w te tm tn ti ta : b_good (b_formulas f w te tm tn ti ta).
Proof.
  unfold b_formulas. apply b_good_and; [apply b_good_closed_formulas|]. apply b_good_all. intro g.
  unfold b_imp. apply b_good_binary; [apply b_good_closed_formulas|apply b_good_subset].
Qed.
Lemma b_good_tags0 w z0 : b_good (b_tags0 w z0).
Proof. unfold b_tags0. apply b_good_and; [apply b_good_omega|apply b_good_empty]. Qed.
Lemma b_good_tags1 w z0 z1 : b_good (b_tags1 w z0 z1).
Proof. unfold b_tags1. apply b_good_and; [apply b_good_tags0|apply b_good_successor]. Qed.
Lemma b_good_tags2 w z0 z1 z2 : b_good (b_tags2 w z0 z1 z2).
Proof. unfold b_tags2. apply b_good_and; [apply b_good_tags1|apply b_good_successor]. Qed.
Lemma b_good_tags3 w z0 z1 z2 z3 : b_good (b_tags3 w z0 z1 z2 z3).
Proof. unfold b_tags3. apply b_good_and; [apply b_good_tags2|apply b_good_successor]. Qed.
Lemma b_good_tags4 w z0 z1 z2 z3 z4 : b_good (b_tags4 w z0 z1 z2 z3 z4).
Proof. unfold b_tags4. apply b_good_and; [apply b_good_tags3|apply b_good_successor]. Qed.
Lemma b_good_sentence_setup w z0 z1 z2 z3 z4 f : b_good (b_sentence_setup w z0 z1 z2 z3 z4 f).
Proof. unfold b_sentence_setup. apply b_good_and; [apply b_good_tags4|apply b_good_formulas]. Qed.

Section SentenceSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma tags_builder_holds rho w z0 z1 z2 z3 z4 n :
  w<n -> z0<n -> z1<n -> z2<n -> z3<n -> z4<n ->
  (b_holds R rho (b_tags4 w z0 z1 z2 z3 z4) n <->
   RelTags R (rho w) (rho z0) (rho z1) (rho z2) (rho z3) (rho z4)).
Proof.
  intros W Z0 Z1 Z2 Z3 Z4. unfold b_tags4,b_tags3,b_tags2,b_tags1,b_tags0,RelTags.
  rewrite !(b_holds_and EM).
  assert (K0 : n <= b_next (b_omega w) n) by apply b_good_omega.
  assert (K1 : n <= b_next (b_tags0 w z0) n) by apply b_good_tags0.
  assert (K2 : n <= b_next (b_tags1 w z0 z1) n) by apply b_good_tags1.
  assert (K3 : n <= b_next (b_tags2 w z0 z1 z2) n) by apply b_good_tags2.
  assert (K4 : n <= b_next (b_tags3 w z0 z1 z2 z3) n) by apply b_good_tags3.
  unfold b_tags3,b_tags2,b_tags1,b_tags0 in K1,K2,K3,K4.
  rewrite (omega_builder_holds EM),empty_builder_holds,!(@successor_builder_holds D R EM) by lia. tauto.
Qed.

Lemma sentence_setup_builder_holds rho w z0 z1 z2 z3 z4 f n :
  w<n -> z0<n -> z1<n -> z2<n -> z3<n -> z4<n -> f<n ->
  (b_holds R rho (b_sentence_setup w z0 z1 z2 z3 z4 f) n <->
   RelSentenceSetup R (rho w) (rho z0) (rho z1) (rho z2) (rho z3) (rho z4) (rho f)).
Proof.
  intros W Z0 Z1 Z2 Z3 Z4 F. unfold b_sentence_setup,RelSentenceSetup. rewrite (b_holds_and EM).
  assert (K : n <= b_next (b_tags4 w z0 z1 z2 z3 z4) n) by apply b_good_tags4.
  rewrite tags_builder_holds,(formulas_builder_holds EM) by lia. reflexivity.
Qed.

Lemma sentence_body_builder_holds rho w z0 z1 z2 z3 z4 f n :
  w<n -> z0<n -> z1<n -> z2<n -> z3<n -> z4<n -> f<n ->
  (b_holds R rho (b_sentence_body w z0 z1 z2 z3 z4 f) n <->
   RelSentenceBody R (rho w) (rho z0) (rho z1) (rho z2) (rho z3) (rho z4) (rho f)).
Proof.
  intros W Z0 Z1 Z2 Z3 Z4 F. unfold b_sentence_body,RelSentenceBody. rewrite (b_holds_and EM).
  assert (K : n <= b_next (b_sentence_setup w z0 z1 z2 z3 z4 f) n) by apply b_good_sentence_setup.
  rewrite sentence_setup_builder_holds,(berkeley_cardinal_builder_holds EM) by lia. reflexivity.
Qed.

Theorem berkeley_sentence_builder_holds rho :
  b_holds R rho b_berkeley_sentence 0 <-> RelBerkeleySentence R.
Proof.
  unfold b_berkeley_sentence,RelBerkeleySentence. rewrite (b_holds_ex EM). split.
  - intros [w H]. rewrite (b_holds_ex EM) in H. destruct H as [z0 H].
    rewrite (b_holds_ex EM) in H. destruct H as [z1 H].
    rewrite (b_holds_ex EM) in H. destruct H as [z2 H].
    rewrite (b_holds_ex EM) in H. destruct H as [z3 H].
    rewrite (b_holds_ex EM) in H. destruct H as [z4 H].
    rewrite (b_holds_ex EM) in H. destruct H as [f H].
    change (b_holds R (push_environment rho 0 [w;z0;z1;z2;z3;z4;f])
      (b_sentence_body 0 1 2 3 4 5 6) 7) in H.
    rewrite sentence_body_builder_holds in H by lia.
    set (sigma := push_environment rho 0 [w;z0;z1;z2;z3;z4;f]) in H.
    assert (W : sigma 0=w) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 0 w eq_refl)).
    assert (Z0 : sigma 1=z0) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 1 z0 eq_refl)).
    assert (Z1 : sigma 2=z1) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 2 z1 eq_refl)).
    assert (Z2 : sigma 3=z2) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 3 z2 eq_refl)).
    assert (Z3 : sigma 4=z3) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 4 z3 eq_refl)).
    assert (Z4 : sigma 5=z4) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 5 z4 eq_refl)).
    assert (F : sigma 6=f) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 6 f eq_refl)).
    rewrite W,Z0,Z1,Z2,Z3,Z4,F in H. now exists w,z0,z1,z2,z3,z4,f.
  - intros [w [z0 [z1 [z2 [z3 [z4 [f H]]]]]]]. exists w.
    rewrite (b_holds_ex EM). exists z0. rewrite (b_holds_ex EM). exists z1.
    rewrite (b_holds_ex EM). exists z2. rewrite (b_holds_ex EM). exists z3.
    rewrite (b_holds_ex EM). exists z4. rewrite (b_holds_ex EM). exists f.
    change (b_holds R (push_environment rho 0 [w;z0;z1;z2;z3;z4;f]) (b_sentence_body 0 1 2 3 4 5 6) 7).
    rewrite sentence_body_builder_holds by lia.
    set (sigma := push_environment rho 0 [w;z0;z1;z2;z3;z4;f]).
    change (RelSentenceBody R (sigma 0) (sigma 1) (sigma 2) (sigma 3) (sigma 4) (sigma 5) (sigma 6)).
    assert (W : sigma 0=w) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 0 w eq_refl)).
    assert (Z0 : sigma 1=z0) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 1 z0 eq_refl)).
    assert (Z1 : sigma 2=z1) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 2 z1 eq_refl)).
    assert (Z2 : sigma 3=z2) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 3 z2 eq_refl)).
    assert (Z3 : sigma 4=z3) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 4 z3 eq_refl)).
    assert (Z4 : sigma 5=z4) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 5 z4 eq_refl)).
    assert (F : sigma 6=f) by (unfold sigma; exact (@push_environment_at D rho 0 [w;z0;z1;z2;z3;z4;f] 6 f eq_refl)).
    now rewrite W,Z0,Z1,Z2,Z3,Z4,F.
Qed.

Theorem candidate_berkeley_relational_semantics rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <-> RelBerkeleySentence R.
Proof. rewrite candidate_berkeley_builder_semantics. apply berkeley_sentence_builder_holds. Qed.
Theorem original_berkeley_relational_semantics rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 original_axioms (Hole 0))) <-> RelBerkeleySentence R.
Proof.
  rewrite original_berkeley_interpretation.
  rewrite <- (builder_plain_semantics R rho (fun _=>False) b_berkeley_sentence 0) by exact (proj1 berkeley_formulas_plain).
  apply berkeley_sentence_builder_holds.
Qed.
End SentenceSemantics.

Print Assumptions berkeley_sentence_builder_holds.
Print Assumptions candidate_berkeley_relational_semantics.
Print Assumptions original_berkeley_relational_semantics.
