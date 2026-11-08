(** First-order predicate selecting pairs (formula, environment) whose truth
    is witnessed by an internally bounded partial evaluation. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxFunction BerkeleySyntaxFormulaSet BerkeleySyntaxZFSeparation BerkeleySyntaxPartialUnion BerkeleySyntaxScope
  BerkeleySyntaxGuardedQuantifiers BerkeleySyntaxPartialWitnessFormula.
Import ListNotations.

Definition partial_value_builder p s e f w m te tm tn ti ta := b_ex (fun g => b_ex (fun h => b_and3
  (b_mem p g) (partial_evaluation_builder h g e f w m te tm tn ti ta) (b_rel h p s))).
Definition truth_member_builder z e f w m te tm tn ti ta := b_ein f (fun p => b_ein e (fun s =>
  b_and (b_pair z p s) (partial_value_builder p s e f w m te tm tn ti ta))).
Definition RelPartialTruthValue {D} (R:D->D->Prop) p s e f w m te tm tn ti ta :=
  exists g h, R p g /\ RelPartialEvaluation R h g e f w m te tm tn ti ta /\ RelGraph R h p s.
Definition RelTruthMember {D} (R:D->D->Prop) z e f w m te tm tn ti ta :=
  exists p s, R p f /\ R s e /\ RelPair R z p s /\ RelPartialTruthValue R p s e f w m te tm tn ti ta.
Definition truth_member_formula := instantiate_formula (fun _=>0)
  (fst (truth_member_builder 2 4 3 5 6 7 8 9 10 11 12)).
Lemma truth_member_output_fresh : fol_free 1 truth_member_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section TruthGraphFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_value_builder_holds rho p s e f w m te tm tn ti ta n :
  p<n -> s<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_value_builder p s e f w m te tm tn ti ta) n <->
   RelPartialTruthValue R (rho p) (rho s) (rho e) (rho f) (rho w) (rho m) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros P S0 E F W M Te Tm Tn Ti Ta. unfold partial_value_builder,RelPartialTruthValue. rewrite (b_holds_ex EM). split.
  - intros [g H]. rewrite (b_holds_ex EM) in H. destruct H as [h H]. unfold b_and3 in H. rewrite !(b_holds_and EM),b_holds_mem in H.
    replace (b_next (b_mem p n) (S(S n))) with (S(S n)) in H by reflexivity.
    assert (K : S(S n) <= b_next (b_and (b_mem p n) (partial_evaluation_builder (S n) n e f w m te tm tn ti ta)) (S(S n)))
      by (apply b_good_and; [apply b_good_mem|apply b_good_partial_evaluation]).
    rewrite (@partial_evaluation_builder_holds D R EM),(relation_builder_holds EM) in H by lia.
    change ((R (push_environment rho n [g;h] p) (push_environment rho n [g;h] n) /\
      RelPartialEvaluation R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] n)
        (push_environment rho n [g;h] e) (push_environment rho n [g;h] f) (push_environment rho n [g;h] w)
        (push_environment rho n [g;h] m) (push_environment rho n [g;h] te) (push_environment rho n [g;h] tm)
        (push_environment rho n [g;h] tn) (push_environment rho n [g;h] ti) (push_environment rho n [g;h] ta)) /\
      RelGraph R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] p) (push_environment rho n [g;h] s)) in H.
    destruct (@push_environment_two D rho n g h) as [Old [G0 H0]].
    rewrite (Old p P),(Old s S0),(Old e E),(Old f F),(Old w W),(Old m M),(Old te Te),(Old tm Tm),(Old tn Tn),(Old ti Ti),(Old ta Ta),G0,H0 in H.
    exists g,h. tauto.
  - intros [g [h H]]. exists g. rewrite (b_holds_ex EM). exists h. unfold b_and3. rewrite !(b_holds_and EM),b_holds_mem.
    replace (b_next (b_mem p n) (S(S n))) with (S(S n)) by reflexivity.
    assert (K : S(S n) <= b_next (b_and (b_mem p n) (partial_evaluation_builder (S n) n e f w m te tm tn ti ta)) (S(S n)))
      by (apply b_good_and; [apply b_good_mem|apply b_good_partial_evaluation]).
    rewrite (@partial_evaluation_builder_holds D R EM),(relation_builder_holds EM) by lia.
    change ((R (push_environment rho n [g;h] p) (push_environment rho n [g;h] n) /\
      RelPartialEvaluation R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] n)
        (push_environment rho n [g;h] e) (push_environment rho n [g;h] f) (push_environment rho n [g;h] w)
        (push_environment rho n [g;h] m) (push_environment rho n [g;h] te) (push_environment rho n [g;h] tm)
        (push_environment rho n [g;h] tn) (push_environment rho n [g;h] ti) (push_environment rho n [g;h] ta)) /\
      RelGraph R (push_environment rho n [g;h] (S n)) (push_environment rho n [g;h] p) (push_environment rho n [g;h] s)).
    destruct (@push_environment_two D rho n g h) as [Old [G0 H0]].
    rewrite (Old p P),(Old s S0),(Old e E),(Old f F),(Old w W),(Old m M),(Old te Te),(Old tm Tm),(Old tn Tn),(Old ti Ti),(Old ta Ta),G0,H0. tauto.
Qed.

Theorem truth_member_builder_holds rho z e f w m te tm tn ti ta n :
  z<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (truth_member_builder z e f w m te tm tn ti ta) n <->
   RelTruthMember R (rho z) (rho e) (rho f) (rho w) (rho m) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros Z E F W M Te Tm Tn Ti Ta. unfold truth_member_builder,RelTruthMember. rewrite (b_holds_ein EM) by exact F. split.
  - intros [p [P H]]. rewrite (b_holds_ein EM) in H by lia. destruct H as [s [S0 H]]. rewrite update_variable_neq in S0 by lia.
    rewrite (b_holds_and EM) in H. assert (K : S(S n) <= b_next (b_pair z n (S n)) (S(S n))) by apply b_good_pair.
    rewrite (pair_builder_holds EM),partial_value_builder_holds in H by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) s) in H.
    assert (Sz : sigma z=rho z) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ste : sigma te=rho te) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stm : sigma tm=rho tm) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stn : sigma tn=rho tn) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sti : sigma ti=rho ti) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sta : sigma ta=rho ta) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=s) by (unfold sigma; apply update_variable_eq).
    rewrite Sz,Se,Sf,Sw,Sm,Ste,Stm,Stn,Sti,Sta,Sp,Ss in H. exists p,s. tauto.
  - intros [p [s [P [S0 [Pair Truth]]]]]. exists p. split; [exact P|]. rewrite (b_holds_ein EM) by lia.
    exists s. split; [rewrite update_variable_neq by lia; exact S0|]. rewrite (b_holds_and EM).
    assert (K : S(S n) <= b_next (b_pair z n (S n)) (S(S n))) by apply b_good_pair.
    rewrite (pair_builder_holds EM),partial_value_builder_holds by lia.
    set (sigma := update_variable (update_variable rho n p) (S n) s).
    change (RelPair R (sigma z) (sigma n) (sigma (S n)) /\
      RelPartialTruthValue R (sigma n) (sigma (S n)) (sigma e) (sigma f) (sigma w) (sigma m)
        (sigma te) (sigma tm) (sigma tn) (sigma ti) (sigma ta)).
    assert (Sz : sigma z=rho z) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma e=rho e) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ste : sigma te=rho te) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stm : sigma tm=rho tm) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stn : sigma tn=rho tn) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sti : sigma ti=rho ti) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sta : sigma ta=rho ta) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=s) by (unfold sigma; apply update_variable_eq).
    rewrite Sz,Se,Sf,Sw,Sm,Ste,Stm,Stn,Sti,Sta,Sp,Ss. now split.
Qed.

Theorem truth_member_formula_holds rho : FolHolds R rho truth_member_formula <->
  RelTruthMember R (rho 2) (rho 4) (rho 3) (rho 5) (rho 6) (rho 7) (rho 8) (rho 9) (rho 10) (rho 11).
Proof.
  change (b_holds R rho (truth_member_builder 2 4 3 5 6 7 8 9 10 11) 12 <->
    RelTruthMember R (rho 2) (rho 4) (rho 3) (rho 5) (rho 6) (rho 7) (rho 8) (rho 9) (rho 10) (rho 11)).
  rewrite truth_member_builder_holds by lia. reflexivity.
Qed.
End TruthGraphFormula.

Print Assumptions truth_member_output_fresh.
Print Assumptions truth_member_formula_holds.
