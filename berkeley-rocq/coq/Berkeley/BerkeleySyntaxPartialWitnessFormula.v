(** First-order definability of a bounded, downward-closed partial evaluation
    and of the existence of one containing a designated internal formula. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxSets
  BerkeleySyntaxFormulaSet BerkeleySyntaxScope BerkeleySyntaxSentence BerkeleySyntaxZFSeparation BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion
  BerkeleySyntaxPartialTruthFormula BerkeleySyntaxPartialDownFormula BerkeleySyntaxGuardedQuantifiers.
Import ListNotations.

Definition partial_evaluation_builder h g e f w m te tm tn ti ta := b_and4
  (b_subset g f) (partial_down_builder g f tn ti ta) (partial_truth_builder h g e f w m te tm tn ti ta)
  (graph_bound_builder h g e).
Definition partial_witness_builder p e f w m te tm tn ti ta := b_ex (fun g => b_ex (fun h =>
  b_and (b_mem p g) (partial_evaluation_builder h g e f w m te tm tn ti ta))).
Definition RelPartialWitness {D} (R:D->D->Prop) p e f w m te tm tn ti ta :=
  exists g h, R p g /\ RelPartialEvaluation R h g e f w m te tm tn ti ta.
Definition partial_witness_formula := instantiate_formula (fun _=>0) (fst (partial_witness_builder 2 3 0 4 5 6 7 8 9 10 11)).
Lemma partial_witness_output_fresh : fol_free 1 partial_witness_formula=false.
Proof. vm_compute. reflexivity. Qed.

Lemma b_good_partial_evaluation h g e f w m te tm tn ti ta : b_good (partial_evaluation_builder h g e f w m te tm tn ti ta).
Proof.
  unfold partial_evaluation_builder,b_and4,b_and3. apply b_good_and; [|apply b_good_graph_bound].
  apply b_good_and; [apply b_good_and; [apply b_good_subset|apply b_good_partial_down]|apply b_good_partial_truth].
Qed.

Section WitnessSemantics.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_evaluation_builder_holds rho h g e f w m te tm tn ti ta n :
  h<n -> g<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_evaluation_builder h g e f w m te tm tn ti ta) n <->
   RelPartialEvaluation R (rho h) (rho g) (rho e) (rho f) (rho w) (rho m) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros H G E F W M Te Tm Tn Ti Ta. unfold partial_evaluation_builder,RelPartialEvaluation,b_and4,b_and3.
  rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (b_subset g f) n) by apply b_good_subset.
  assert (K2 : n <= b_next (b_and (b_subset g f) (partial_down_builder g f tn ti ta)) n)
    by (apply b_good_and; [apply b_good_subset|apply b_good_partial_down]).
  assert (K3 : n <= b_next (b_and (b_and (b_subset g f) (partial_down_builder g f tn ti ta))
    (partial_truth_builder h g e f w m te tm tn ti ta)) n)
    by (apply b_good_and; [apply b_good_and; [apply b_good_subset|apply b_good_partial_down]|apply b_good_partial_truth]).
  rewrite subset_builder_holds,(@partial_down_builder_holds D R EM),(@partial_truth_builder_holds D R EM),
    (@graph_bound_builder_holds D R EM) by lia. tauto.
Qed.

Theorem partial_witness_builder_holds rho p e f w m te tm tn ti ta n :
  p<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_witness_builder p e f w m te tm tn ti ta) n <->
   RelPartialWitness R (rho p) (rho e) (rho f) (rho w) (rho m) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros P E F W M Te Tm Tn Ti Ta. unfold partial_witness_builder,RelPartialWitness. rewrite (b_holds_ex EM). split.
  - intros [g H]. rewrite (b_holds_ex EM) in H. destruct H as [h H]. rewrite (b_holds_and EM),b_holds_mem in H.
    replace (b_next (b_mem p n) (S(S n))) with (S(S n)) in H by reflexivity.
    rewrite partial_evaluation_builder_holds in H by lia.
    change (R (push_environment rho n [g;h] p) (push_environment rho n [g;h] n) /\
      RelPartialEvaluation R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] n)
        (push_environment rho n [g;h] e) (push_environment rho n [g;h] f) (push_environment rho n [g;h] w)
        (push_environment rho n [g;h] m) (push_environment rho n [g;h] te) (push_environment rho n [g;h] tm)
        (push_environment rho n [g;h] tn) (push_environment rho n [g;h] ti) (push_environment rho n [g;h] ta)) in H.
    destruct (@push_environment_two D rho n g h) as [Old [G0 H0]].
    rewrite (Old p P),(Old e E),(Old f F),(Old w W),(Old m M),(Old te Te),(Old tm Tm),(Old tn Tn),(Old ti Ti),(Old ta Ta),G0,H0 in H.
    now exists g,h.
  - intros [g [h H]]. exists g. rewrite (b_holds_ex EM). exists h. rewrite (b_holds_and EM),b_holds_mem.
    replace (b_next (b_mem p n) (S(S n))) with (S(S n)) by reflexivity.
    rewrite partial_evaluation_builder_holds by lia.
    change (R (push_environment rho n [g;h] p) (push_environment rho n [g;h] n) /\
      RelPartialEvaluation R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] n)
        (push_environment rho n [g;h] e) (push_environment rho n [g;h] f) (push_environment rho n [g;h] w)
        (push_environment rho n [g;h] m) (push_environment rho n [g;h] te) (push_environment rho n [g;h] tm)
        (push_environment rho n [g;h] tn) (push_environment rho n [g;h] ti) (push_environment rho n [g;h] ta)).
    destruct (@push_environment_two D rho n g h) as [Old [G0 H0]].
    rewrite (Old p P),(Old e E),(Old f F),(Old w W),(Old m M),(Old te Te),(Old tm Tm),(Old tn Tn),(Old ti Ti),(Old ta Ta),G0,H0. exact H.
Qed.

Theorem partial_witness_formula_holds rho : FolHolds R rho partial_witness_formula <->
  RelPartialWitness R (rho 2) (rho 3) (rho 0) (rho 4) (rho 5) (rho 6) (rho 7) (rho 8) (rho 9) (rho 10).
Proof.
  change (b_holds R rho (partial_witness_builder 2 3 0 4 5 6 7 8 9 10) 11 <->
    RelPartialWitness R (rho 2) (rho 3) (rho 0) (rho 4) (rho 5) (rho 6) (rho 7) (rho 8) (rho 9) (rho 10)).
  rewrite partial_witness_builder_holds by lia. reflexivity.
Qed.
End WitnessSemantics.

Print Assumptions partial_witness_output_fresh.
Print Assumptions partial_witness_formula_holds.
