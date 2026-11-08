(** Uniqueness of internal omega, syntax tags, formula set, and environment
    set under extensionality. Truth graphs need only agree on the relevant
    formula/environment domain, as proved separately. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import BerkeleySyntaxRepresentations BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxFormulaSet
  BerkeleySyntaxEnvironment BerkeleySyntaxSentence BerkeleySyntaxNumerals BerkeleySyntaxTags.
Import ListNotations.

Theorem relational_omega_unique {D} (R:D->D->Prop) a b :
  RelExtensional R -> RelOmega R a -> RelOmega R b -> a=b.
Proof.
  intros Ext [A MinA] [B MinB]. apply Ext. intro x. split; [apply (MinA b B)|apply (MinB a A)].
Qed.
Theorem relational_formula_set_unique {D} (R:D->D->Prop) f g w te tm tn ti ta :
  RelExtensional R -> RelFormulas R f w te tm tn ti ta -> RelFormulas R g w te tm tn ti ta -> f=g.
Proof.
  intros Ext [F MinF] [G MinG]. apply Ext. intro x. split; [apply (MinF g G)|apply (MinG f F)].
Qed.
Theorem relational_tag_chains_unique {D} (R:D->D->Prop) w a0 a1 a2 a3 a4 w' b0 b1 b2 b3 b4 :
  RelExtensional R -> RelTags R w a0 a1 a2 a3 a4 -> RelTags R w' b0 b1 b2 b3 b4 ->
  w=w' /\ a0=b0 /\ a1=b1 /\ a2=b2 /\ a3=b3 /\ a4=b4.
Proof.
  intros Ext A B. assert (W : w=w') by (eapply relational_omega_unique; [exact Ext|exact (proj1 A)|exact (proj1 B)]).
  assert (E0 : a0=b0) by (eapply (numeral_unique R Ext 0); [eapply actual_tags_numerals; [exact A|reflexivity]|eapply actual_tags_numerals; [exact B|reflexivity]]).
  assert (E1 : a1=b1) by (eapply (numeral_unique R Ext 1); [eapply actual_tags_numerals; [exact A|reflexivity]|eapply actual_tags_numerals; [exact B|reflexivity]]).
  assert (E2 : a2=b2) by (eapply (numeral_unique R Ext 2); [eapply actual_tags_numerals; [exact A|reflexivity]|eapply actual_tags_numerals; [exact B|reflexivity]]).
  assert (E3 : a3=b3) by (eapply (numeral_unique R Ext 3); [eapply actual_tags_numerals; [exact A|reflexivity]|eapply actual_tags_numerals; [exact B|reflexivity]]).
  assert (E4 : a4=b4) by (eapply (numeral_unique R Ext 4); [eapply actual_tags_numerals; [exact A|reflexivity]|eapply actual_tags_numerals; [exact B|reflexivity]]).
  tauto.
Qed.

Print Assumptions relational_omega_unique.
Print Assumptions relational_formula_set_unique.
Print Assumptions relational_tag_chains_unique.
