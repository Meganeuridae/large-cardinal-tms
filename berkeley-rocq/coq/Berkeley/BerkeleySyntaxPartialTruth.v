(** Overlap uniqueness for downward-closed partial Tarski valuations. These
    hypotheses and the induction property are first-order expressible; the
    result applies to all internal formulas, not only external finite trees. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment BerkeleySyntaxSatisfactionAtomic
  BerkeleySyntaxSatisfactionUnique BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation BerkeleySyntaxFormulaInduction.
Import ListNotations.

Definition RelPartialDownward {D} (R:D->D->Prop) g f tn ti ta :=
  (forall p q, R p g -> R q f -> RelPair R p tn q -> R q g) /\
  (forall p q r, R p g -> R q f -> R r f -> RelNode2 R p ti q r -> R q g /\ R r g) /\
  (forall p x q, R p g -> R q f -> RelNode2 R p ta x q -> R q g).
Definition RelPartialTruth {D} (R:D->D->Prop) h g e f w m te tm tn ti ta := forall s, R s e ->
  (forall u v x y p, R p g -> R u w -> R v w -> R x m -> R y m ->
    RelGraph R s u x -> RelGraph R s v y -> RelNode2 R p te u v -> (RelGraph R h p s <-> x=y)) /\
  (forall u v x y p, R p g -> R u w -> R v w -> R x m -> R y m ->
    RelGraph R s u x -> RelGraph R s v y -> RelNode2 R p tm u v -> (RelGraph R h p s <-> R x y)) /\
  (forall p q, R q g -> R p f -> RelPair R q tn p -> (RelGraph R h q s <-> ~RelGraph R h p s)) /\
  (forall p q r, R r g -> R p f -> R q f -> RelNode2 R r ti p q ->
    (RelGraph R h r s <-> (RelGraph R h p s -> RelGraph R h q s))) /\
  (forall u p q, R q g -> R u w -> R p f -> RelNode2 R q ta u p ->
    (RelGraph R h q s <-> forall t, R t e -> RelUpdate R s t u w m -> RelGraph R h p t)).
Definition partial_agreement_builder p g1 g2 e h1 h2 :=
  b_imp (b_and (b_mem p g1) (b_mem p g2)) (agreement_builder p e h1 h2).
Definition partial_agreement_formula :=
  instantiate_formula (fun _=>0) (fst (partial_agreement_builder 2 3 4 5 6 7 8)).
Lemma partial_agreement_output_fresh : fol_free 1 partial_agreement_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section PartialAgreement.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_agreement_formula_holds rho : FolHolds R rho partial_agreement_formula <->
  (R (rho 2) (rho 3) -> R (rho 2) (rho 4) ->
    RelSatisfactionAgreement R (rho 2) (rho 5) (rho 6) (rho 7)).
Proof.
  change (b_holds R rho (partial_agreement_builder 2 3 4 5 6 7) 8 <->
    (R (rho 2) (rho 3) -> R (rho 2) (rho 4) ->
      RelSatisfactionAgreement R (rho 2) (rho 5) (rho 6) (rho 7))).
  unfold partial_agreement_builder. rewrite b_holds_imp,(b_holds_and EM),!b_holds_mem.
  replace (b_next (b_and (b_mem 2 3) (b_mem 2 4)) 8) with 8 by reflexivity.
  rewrite (@agreement_builder_holds D R EM) by lia. tauto.
Qed.
End PartialAgreement.

Section PartialUniqueness.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_truth_agrees_on_overlap f w m e te tm tn ti ta g1 g2 h1 h2 :
  RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  RelPartialDownward R g1 f tn ti ta -> RelPartialDownward R g2 f tn ti ta ->
  RelPartialTruth R h1 g1 e f w m te tm tn ti ta -> RelPartialTruth R h2 g2 e f w m te tm tn ti ta ->
  forall p s, R p f -> R p g1 -> R p g2 -> R s e -> (RelGraph R h1 p s <-> RelGraph R h2 p s).
Proof.
  intros Formulas Env [NDown1 [IDown1 ADown1]] [NDown2 [IDown2 ADown2]] Sat1 Sat2.
  set (rho := update_variable (update_variable (update_variable (update_variable (update_variable
    (fun _ : nat => f) 3 g1) 4 g2) 5 e) 6 h1) 7 h2).
  assert (Interpret : forall p, RelFormulaProperty R partial_agreement_formula rho p <->
    (R p g1 -> R p g2 -> RelSatisfactionAgreement R p e h1 h2)).
  { intro p. unfold RelFormulaProperty. rewrite (partial_agreement_formula_holds R EM). unfold rho.
    cbv [update_variable Nat.eqb]. reflexivity. }
  assert (AllAgreement : forall p, R p f -> RelFormulaProperty R partial_agreement_formula rho p).
  { eapply (zf_internal_formula_induction R EM Model f w te tm tn ti ta partial_agreement_formula rho);
      [reflexivity|exact partial_agreement_output_fresh|exact Formulas| | | | |].
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)). intros P1 P2 s S.
      destruct (proj1 (Env s) S) as [_ Total]. destruct (Total x X) as [a [A [Ga _]]].
      destruct (Total y Y) as [b [B [Gb _]]].
      destruct (Sat1 s S) as [Eq1 _]. destruct (Sat2 s S) as [Eq2 _].
      specialize (Eq1 x y a b p P1 X Y A B Ga Gb Node). specialize (Eq2 x y a b p P2 X Y A B Ga Gb Node). tauto.
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)). intros P1 P2 s S.
      destruct (proj1 (Env s) S) as [_ Total]. destruct (Total x X) as [a [A [Ga _]]].
      destruct (Total y Y) as [b [B [Gb _]]].
      destruct (Sat1 s S) as [_ [Mem1 _]]. destruct (Sat2 s S) as [_ [Mem2 _]].
      specialize (Mem1 x y a b p P1 X Y A B Ga Gb Node). specialize (Mem2 x y a b p P2 X Y A B Ga Gb Node). tauto.
    - intros q p Qf Qp Pf Pair. apply (proj2 (Interpret p)). intros P1 P2 s S.
      pose proof (proj1 (Interpret q) Qp (NDown1 p q P1 Qf Pair) (NDown2 p q P2 Qf Pair) s S) as IH.
      destruct (Sat1 s S) as [_ [_ [N1 _]]]. destruct (Sat2 s S) as [_ [_ [N2 _]]].
      specialize (N1 q p P1 Qf Pair). specialize (N2 q p P2 Qf Pair). tauto.
    - intros q r p Qf Qp Rf Rp Pf Node. apply (proj2 (Interpret p)). intros P1 P2 s S.
      destruct (IDown1 p q r P1 Qf Rf Node) as [Q1 R1]. destruct (IDown2 p q r P2 Qf Rf Node) as [Q2 R2].
      pose proof (proj1 (Interpret q) Qp Q1 Q2 s S) as IH1. pose proof (proj1 (Interpret r) Rp R1 R2 s S) as IH2.
      destruct (Sat1 s S) as [_ [_ [_ [I1 _]]]]. destruct (Sat2 s S) as [_ [_ [_ [I2 _]]]].
      specialize (I1 q r p P1 Qf Rf Node). specialize (I2 q r p P2 Qf Rf Node). tauto.
    - intros x q p X Qf Qp Pf Node. apply (proj2 (Interpret p)). intros P1 P2 s S.
      pose proof (proj1 (Interpret q) Qp (ADown1 p x q P1 Qf Node) (ADown2 p x q P2 Qf Node)) as IH.
      destruct (Sat1 s S) as [_ [_ [_ [_ A1]]]]. destruct (Sat2 s S) as [_ [_ [_ [_ A2]]]].
      specialize (A1 x q p P1 X Qf Node). specialize (A2 x q p P2 X Qf Node).
      rewrite A1,A2. split; intros H t T Up; [apply (proj1 (IH t T))|apply (proj2 (IH t T))]; now apply H. }
  intros p s P P1 P2 S. exact ((proj1 (Interpret p)) (AllAgreement p P) P1 P2 s S).
Qed.
End PartialUniqueness.

Print Assumptions partial_agreement_formula_holds.
Print Assumptions zf_partial_truth_agrees_on_overlap.
