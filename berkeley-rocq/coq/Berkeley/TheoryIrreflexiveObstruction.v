(** The universal distinctor premise is not a free-standing logical bridge.
    It already entails the machine's contradiction target. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofSearchSyntax ProofFormula ProofPresentation
  LogicBridge LogicQuantifier LogicFresh TheoryIrreflexiveND TheoryIrreflexiveHilbert.
Import ListNotations.

Definition literal_below n x := match x with V k => k <? n | P _ => true end.
Fixpoint literals_below n f :=
  match f with
  | Atom _ x y => literal_below n x && literal_below n y
  | Neg p => literals_below n p
  | Imp p q => literals_below n p && literals_below n q
  | All x p => literal_below n x && literals_below n p
  | Hole _ => true
  end.

Lemma candidate_literals_below_11 : forallb (literals_below 11) candidate_axioms=true.
Proof. vm_compute. reflexivity. Qed.

Lemma rename_bounded_variable rho n vars x :
  (forall k, k<n -> rho k=k) -> literal_below n x=true ->
  rho (independent_variable vars x) = independent_variable (fun k => rho (vars k)) x.
Proof.
  intros Fix B. destruct x; cbn [literal_below independent_variable] in *; auto.
  apply Fix, Nat.ltb_lt, B.
Qed.

Lemma rename_bounded_instance rho n vars holes f :
  (forall k, k<n -> rho k=k) -> literals_below n f=true ->
  rename_formula rho (independent_instance vars holes f) =
  independent_instance (fun k => rho (vars k)) (fun k => rename_formula rho (holes k)) f.
Proof.
  intros Fix. induction f as [b x y|p IH|p IH q JH|x p IH|h]; cbn [literals_below]; intro B.
  - apply andb_true_iff in B as [Bx By]. destruct b; cbn [rename_formula independent_instance];
      rewrite ?(rename_bounded_variable rho n vars x Fix Bx),
              ?(rename_bounded_variable rho n vars y Fix By); reflexivity.
  - cbn [rename_formula independent_instance]. f_equal. now apply IH.
  - apply andb_true_iff in B as [Bp Bq]. cbn [rename_formula independent_instance].
    f_equal; [now apply IH|now apply JH].
  - apply andb_true_iff in B as [Bx Bp]. cbn [rename_formula independent_instance].
    rewrite (rename_bounded_variable rho n vars x Fix Bx). f_equal. now apply IH.
  - reflexivity.
Qed.

Theorem presented_renaming_fixing_literals rho f :
  (forall k, k<11 -> rho k=k) -> PresentedProvable f -> PresentedProvable (rename_formula rho f).
Proof.
  intros Fix H. induction H as [|i f vars holes A|p q Major IHm Minor IHn|x p P IH].
  - cbn [rename_formula]. rewrite Fix by lia. apply presented_reflexivity.
  - pose proof (proj1 (forallb_forall _ _) candidate_literals_below_11 f
      (nth_error_In _ _ A)) as B.
    rewrite (rename_bounded_instance rho 11 vars holes f Fix B). eapply presented_axiom; exact A.
  - cbn [rename_formula]. eapply presented_mp; eassumption.
  - cbn [rename_formula]. now apply presented_gen.
Qed.

Lemma logical_b10_local x y p : LogicalProvable
  (FImp (FAll x (FImp (FEqual x y) (FAll x p))) p).
Proof.
  change (LogicalProvable (independent_instance (logic_vars x y 0) (fun _=>p)
    (nth 9 logical_schemas (Hole 0)))).
  eapply logical_axiom with (i:=9). reflexivity.
Qed.

(** Equality reflexivity is obtained without any distinctor premise. *)
Theorem presented_equality_reflexive_unconditional x : PresentedProvable (FEqual x x).
Proof.
  set (E := FEqual x x). set (A := FAll x E). set (D := FNeg A).
  assert (T : PresentedProvable (FImp (FAll x D) (FImp E A))).
  { apply hc_finish,hc_deduction,hc_deduction.
    eapply hc_mp.
    - eapply hc_mp.
      + eapply hc_mp; [apply hc_logical,logical_b9|].
        eapply hc_mp; [apply hc_logical,logical_b5|apply hc_hyp; cbn; auto].
      + eapply hc_mp; [apply hc_logical,logical_b5|apply hc_hyp; cbn; auto].
    - apply hc_hyp; now left. }
  assert (U : PresentedProvable (FImp (FAll x D) (FAll x (FImp E A)))).
  { eapply presented_mp; [apply logical_embeds_in_presented,logical_b4|now apply presented_gen]. }
  assert (V : PresentedProvable (FImp (FAll x D) E)).
  { eapply presented_syllogism; [exact U|].
    unfold E,A. apply logical_embeds_in_presented,logical_b10_local. }
  change (PresentedProvable E). apply hc_finish,hc_classical.
  eapply hc_explosion with (p:=E).
  - eapply hc_mp; [apply hc_theorem; exact V|].
    eapply hc_mp; [apply hc_logical,logical_b7|apply hc_hyp; now left].
  - apply hc_hyp; now left.
Qed.

Definition collapse_12_to_11 k := if Nat.eqb k 12 then 11 else k.

Theorem high_distinctor_implies_presented_target :
  PresentedProvable (distinctor 11 12) -> PresentedProvable (FMember 0 0).
Proof.
  intro H.
  pose proof (presented_renaming_fixing_literals collapse_12_to_11 (distinctor 11 12)) as R.
  assert (Fix : forall k, k<11 -> collapse_12_to_11 k=k).
  { intros k B. unfold collapse_12_to_11.
    destruct (Nat.eqb k 12) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity]. }
  specialize (R Fix H). cbn [rename_formula distinctor collapse_12_to_11] in R.
  apply hc_finish. eapply hc_explosion with (p:=FAll 11 (FEqual 11 11)).
  - apply hc_theorem,presented_gen,presented_equality_reflexive_unconditional.
  - apply hc_theorem. exact R.
Qed.

Theorem all_distinctors_imply_numeric_inconsistent :
  (forall x y, x<>y -> PresentedProvable (distinctor x y)) -> NumericInconsistent.
Proof.
  intro All. apply numeric_target_iff_presented_target.
  apply high_distinctor_implies_presented_target,All. lia.
Qed.

Print Assumptions candidate_literals_below_11.
Print Assumptions presented_renaming_fixing_literals.
Print Assumptions presented_equality_reflexive_unconditional.
Print Assumptions high_distinctor_implies_presented_target.
Print Assumptions all_distinctors_imply_numeric_inconsistent.
