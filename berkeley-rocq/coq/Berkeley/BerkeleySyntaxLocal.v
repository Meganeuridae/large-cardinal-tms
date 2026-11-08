(** Relational interpretation of the local truth-set and embedding witnesses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntax BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection BerkeleySyntaxFormulaSet
  BerkeleySyntaxEnvironment BerkeleySyntaxElementary BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxWitnesses FormulaSemantics.
Import ListNotations.

Definition RelBerkeleyLocal {D} (R:D->D->Prop) d m f w te tm tn ti ta :=
  exists e sat, RelEnvironments R e w m /\ RelSatisfaction R sat e f w m te tm tn ti ta /\
    RelBerkeleyWitnesses R d m e f w sat.

Lemma b_good_environments e w m : b_good (b_environments e w m).
Proof.
  unfold b_environments. apply b_good_all. intro s. unfold b_iff.
  apply b_good_binary; [apply b_good_mem|apply b_good_function].
Qed.
Lemma b_good_elementary j m e f w sat : b_good (b_elementary j m e f w sat).
Proof.
  unfold b_elementary. apply b_good_and; [apply b_good_function|].
  apply b_good_ain. intro p. apply b_good_ain. intro s. apply b_good_ain. intro t.
  unfold b_imp,b_iff. apply b_good_binary; [apply b_good_image_environment|].
  apply b_good_binary; apply b_good_rel.
Qed.
Lemma b_good_witnesses d m e f w sat : b_good (b_berkeley_witnesses d m e f w sat).
Proof.
  unfold b_berkeley_witnesses. apply b_good_ain. intro eta. apply b_good_ex. intro j. apply b_good_ex. intro k.
  apply b_good_and; [apply b_good_critical|apply b_good_elementary].
Qed.
Lemma b_good_local d m f w te tm tn ti ta : b_good (b_berkeley_local d m f w te tm tn ti ta).
Proof.
  unfold b_berkeley_local. apply b_good_ex. intro e. apply b_good_ex. intro sat. unfold b_and3.
  apply b_good_and; [apply b_good_and; [apply b_good_environments|apply b_good_satisfaction]|apply b_good_witnesses].
Qed.

Section LocalSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem local_builder_holds rho d m f w te tm tn ti ta n :
  d<n -> m<n -> f<n -> w<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (b_berkeley_local d m f w te tm tn ti ta) n <->
   RelBerkeleyLocal R (rho d) (rho m) (rho f) (rho w) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros D0 M F W Te Tm Tn Ti Ta. unfold b_berkeley_local,RelBerkeleyLocal.
  rewrite (b_holds_ex EM). split.
  - intros [e H]. rewrite (b_holds_ex EM) in H. destruct H as [sat H]. unfold b_and3 in H.
    rewrite !(b_holds_and EM) in H.
    assert (K1 : S(S n) <= b_next (b_environments n w m) (S(S n))) by apply b_good_environments.
    assert (K2 : S(S n) <= b_next (b_and (b_environments n w m)
      (b_satisfaction (S n) n f w m te tm tn ti ta)) (S(S n)))
      by (apply b_good_and; [apply b_good_environments|apply b_good_satisfaction]).
    rewrite (environments_builder_holds EM),(satisfaction_builder_holds EM),(witnesses_builder_holds EM) in H by lia.
    set (sigma := update_variable (update_variable rho n e) (S n) sat) in H.
    assert (Sd : sigma d=rho d) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ste : sigma te=rho te) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stm : sigma tm=rho tm) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stn : sigma tn=rho tn) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sti : sigma ti=rho ti) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sta : sigma ta=rho ta) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma n=e) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=sat) by (unfold sigma; apply update_variable_eq).
    rewrite Sd,Sm,Sf,Sw,Ste,Stm,Stn,Sti,Sta,Se,Ss in H. exists e,sat. tauto.
  - intros [e [sat H]]. exists e. rewrite (b_holds_ex EM). exists sat. unfold b_and3.
    rewrite !(b_holds_and EM).
    assert (K1 : S(S n) <= b_next (b_environments n w m) (S(S n))) by apply b_good_environments.
    assert (K2 : S(S n) <= b_next (b_and (b_environments n w m)
      (b_satisfaction (S n) n f w m te tm tn ti ta)) (S(S n)))
      by (apply b_good_and; [apply b_good_environments|apply b_good_satisfaction]).
    rewrite (environments_builder_holds EM),(satisfaction_builder_holds EM),(witnesses_builder_holds EM) by lia.
    set (sigma := update_variable (update_variable rho n e) (S n) sat).
    change ((RelEnvironments R (sigma n) (sigma w) (sigma m) /\
      RelSatisfaction R (sigma (S n)) (sigma n) (sigma f) (sigma w) (sigma m)
        (sigma te) (sigma tm) (sigma tn) (sigma ti) (sigma ta)) /\
      RelBerkeleyWitnesses R (sigma d) (sigma m) (sigma n) (sigma f) (sigma w) (sigma (S n))).
    assert (Sd : sigma d=rho d) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sf : sigma f=rho f) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ste : sigma te=rho te) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stm : sigma tm=rho tm) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Stn : sigma tn=rho tn) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sti : sigma ti=rho ti) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sta : sigma ta=rho ta) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Se : sigma n=e) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=sat) by (unfold sigma; apply update_variable_eq).
    rewrite Sd,Sm,Sf,Sw,Ste,Stm,Stn,Sti,Sta,Se,Ss. tauto.
Qed.
End LocalSemantics.

Print Assumptions local_builder_holds.
