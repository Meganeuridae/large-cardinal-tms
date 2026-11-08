(** A structural first-order presentation of the exact axiom list. Formula
    and individual-variable parameters are independent in this calculus.
    The finite separation certificate justifies their shared numeric slots. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ConstructorStreams ProofSearchSyntax ProofFormula.
Import ListNotations.

Definition independent_variable vars x := match x with V n => n | P n => vars n end.
Fixpoint independent_instance vars holes f :=
  match f with
  | Atom b x y => (if b then FMember else FEqual) (independent_variable vars x) (independent_variable vars y)
  | Neg p => FNeg (independent_instance vars holes p)
  | Imp p q => FImp (independent_instance vars holes p) (independent_instance vars holes q)
  | All x p => FAll (independent_variable vars x) (independent_instance vars holes p)
  | Hole n => holes n
  end.
Definition var_mentions n x := match x with V _ => false | P m => Nat.eqb n m end.
Fixpoint variable_mentions n f :=
  match f with
  | Atom _ x y => var_mentions n x || var_mentions n y
  | Neg p => variable_mentions n p
  | Imp p q => variable_mentions n p || variable_mentions n q
  | All x p => var_mentions n x || variable_mentions n p
  | Hole _ => false
  end.
Fixpoint hole_mentions n f :=
  match f with
  | Atom _ _ _ => false
  | Neg p => hole_mentions n p
  | Imp p q => hole_mentions n p || hole_mentions n q
  | All _ p => hole_mentions n p
  | Hole m => Nat.eqb n m
  end.
Definition parameter_in_range n := (1<=?n) && (n<=?3).
Definition supported_var x := match x with V _ => true | P n => parameter_in_range n end.
Fixpoint supported_formula f :=
  match f with
  | Atom _ x y => supported_var x && supported_var y
  | Neg p => supported_formula p
  | Imp p q => supported_formula p && supported_formula q
  | All x p => supported_var x && supported_formula p
  | Hole n => parameter_in_range n
  end.
Definition separated_roles f :=
  forallb (fun n => negb (variable_mentions n f && hole_mentions n f)) [1;2;3].
Lemma candidate_parameter_certificate :
  forallb (fun f => supported_formula f && separated_roles f) candidate_axioms = true.
Proof. vm_compute. reflexivity. Qed.
Lemma range_bounds n : parameter_in_range n=true -> 1<=n<=3.
Proof. unfold parameter_in_range. rewrite andb_true_iff,!Nat.leb_le. tauto. Qed.
Lemma supported_var_mentions x n : supported_var x=true -> var_mentions n x=true -> 1<=n<=3.
Proof. destruct x; cbn; [discriminate|]. intros H E. apply Nat.eqb_eq in E. subst. now apply range_bounds. Qed.
Lemma variable_mentions_supported f n : supported_formula f=true -> variable_mentions n f=true -> 1<=n<=3.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|m]; cbn.
  - rewrite andb_true_iff,orb_true_iff. intros [X Y] [M|M]; [exact (supported_var_mentions x n X M)|exact (supported_var_mentions y n Y M)].
  - apply IH.
  - rewrite andb_true_iff,orb_true_iff. intros [P Q] [M|M]; auto.
  - rewrite andb_true_iff,orb_true_iff. intros [X P] [M|M]; [eapply supported_var_mentions; eassumption|auto].
  - discriminate.
Qed.
Lemma hole_mentions_supported f n : supported_formula f=true -> hole_mentions n f=true -> 1<=n<=3.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|m]; cbn.
  - discriminate.
  - apply IH.
  - rewrite andb_true_iff,orb_true_iff. intros [P Q] [M|M]; auto.
  - rewrite andb_true_iff. intros [_ P]. auto.
  - intros H E. apply Nat.eqb_eq in E. subst. now apply range_bounds.
Qed.
Lemma roles_do_not_overlap f n : separated_roles f=true -> 1<=n<=3 ->
  variable_mentions n f=true -> hole_mentions n f=false.
Proof.
  intros Sep Bounds V. unfold separated_roles in Sep.
  assert (I : In n [1;2;3]) by (cbn; lia).
  pose proof (proj1 (forallb_forall _ _) Sep n I) as H.
  cbn beta in H. rewrite V in H. cbn in H. now apply negb_true_iff in H.
Qed.

Lemma variable_code_agrees params vars x :
  (forall n, var_mentions n x=true -> params n=vars n) ->
  variable_value params x = independent_variable vars x.
Proof. destruct x; cbn; auto. intro H. apply H,Nat.eqb_refl. Qed.
Theorem encode_independent_instance params vars holes f :
  (forall n, variable_mentions n f=true -> params n=vars n) ->
  (forall n, hole_mentions n f=true -> params n=encode_formula (holes n)) ->
  formula_code params f = encode_formula (independent_instance vars holes f).
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|n]; intros V H;
    cbn [formula_code independent_instance encode_formula].
  - assert (X : variable_value params x=independent_variable vars x).
    { apply variable_code_agrees. intros k K. apply V. cbn. apply orb_true_iff. now left. }
    assert (Y : variable_value params y=independent_variable vars y).
    { apply variable_code_agrees. intros k K. apply V. cbn. apply orb_true_iff. now right. }
    rewrite X,Y. destruct b; reflexivity.
  - unfold code_neg. f_equal. apply IH; assumption.
  - unfold code_imp. f_equal. f_equal.
    + apply IH; intros k K; [apply V|apply H]; cbn; apply orb_true_iff; now left.
    + apply JH; intros k K; [apply V|apply H]; cbn; apply orb_true_iff; now right.
  - unfold code_all. f_equal. f_equal.
    + apply variable_code_agrees. intros k K. apply V. cbn. apply orb_true_iff. now left.
    + apply IH.
      * intros k K. apply V. cbn. apply orb_true_iff. now right.
      * exact H.
  - apply H,Nat.eqb_refl.
Qed.

Definition chosen_parameter f vars holes n :=
  if hole_mentions n f then encode_formula (holes n) else vars n.
Lemma instruction_params_agree f vars holes n : 1<=n<=3 ->
  instruction_params (chosen_parameter f vars holes 1)
    (chosen_parameter f vars holes 2) (chosen_parameter f vars holes 3) n =
  chosen_parameter f vars holes n.
Proof. intros H. destruct n as [|[|[|[|n]]]]; try lia; reflexivity. Qed.
Theorem independent_axiom_has_numeric_instance i f vars holes :
  nth_error candidate_axioms i=Some f ->
  exists a b c, instantiated_axiom i a b c = Some (encode_formula (independent_instance vars holes f)).
Proof.
  intro E. pose proof (proj1 (forallb_forall _ _) candidate_parameter_certificate f
      (nth_error_In _ _ E)) as Valid.
  apply andb_true_iff in Valid as [Supported Separated].
  exists (chosen_parameter f vars holes 1),(chosen_parameter f vars holes 2),(chosen_parameter f vars holes 3).
  unfold instantiated_axiom. rewrite E. cbn [option_map]. f_equal.
  apply encode_independent_instance; intros n Occurs.
  - rewrite instruction_params_agree by (eapply variable_mentions_supported; eassumption).
    unfold chosen_parameter. rewrite (roles_do_not_overlap f n Separated
      (variable_mentions_supported f n Supported Occurs) Occurs). reflexivity.
  - rewrite instruction_params_agree by (eapply hole_mentions_supported; eassumption).
    unfold chosen_parameter. now rewrite Occurs.
Qed.

Inductive PresentedProvable : fol_formula -> Prop :=
| presented_reflexivity : PresentedProvable (FEqual 0 0)
| presented_axiom i f vars holes : nth_error candidate_axioms i=Some f ->
    PresentedProvable (independent_instance vars holes f)
| presented_mp p q : PresentedProvable (FImp p q) -> PresentedProvable p -> PresentedProvable q
| presented_gen x p : PresentedProvable p -> PresentedProvable (FAll x p).

Lemma numeric_instance_structural params f : instantiate_formula params f =
  independent_instance params (fun n => decode_formula (params n)) f.
Proof. induction f; cbn [instantiate_formula independent_instance]; unfold variable_value,independent_variable in *; congruence. Qed.
Theorem numeric_proof_decodes n : NumericProvable n -> PresentedProvable (decode_formula n).
Proof.
  intro H. induction H as [|i a b c n E|p q Major IHm Minor IHp|x p P IH].
  - change (PresentedProvable (FEqual 0 0)). constructor.
  - unfold instantiated_axiom in E. destruct (nth_error candidate_axioms i) as [f|] eqn:F;
      [|discriminate]. inversion E; subst n.
    rewrite decode_formula_code,numeric_instance_structural. eapply presented_axiom; exact F.
  - rewrite decode_imp in IHm. eapply presented_mp; eassumption.
  - rewrite decode_all. now apply presented_gen.
Qed.
Theorem presented_proof_encodes f : PresentedProvable f -> NumericProvable (encode_formula f).
Proof.
  intro H. induction H as [|i f vars holes E|p q Major IHm Minor IHp|x p P IH].
  - change (NumericProvable 0). constructor.
  - destruct (independent_axiom_has_numeric_instance i f vars holes E) as [a [b [c N]]].
    eapply numeric_axiom; exact N.
  - cbn [encode_formula] in IHm. eapply numeric_mp; eassumption.
  - cbn [encode_formula]. now apply numeric_gen.
Qed.
Theorem numeric_target_iff_presented_target :
  NumericInconsistent <-> PresentedProvable (FMember 0 0).
Proof.
  split; intro H.
  - pose proof (numeric_proof_decodes 1 H) as P. exact P.
  - pose proof (presented_proof_encodes _ H) as P. exact P.
Qed.

Print Assumptions candidate_parameter_certificate.
Print Assumptions independent_axiom_has_numeric_instance.
Print Assumptions numeric_proof_decodes.
Print Assumptions presented_proof_encodes.
Print Assumptions numeric_target_iff_presented_target.
