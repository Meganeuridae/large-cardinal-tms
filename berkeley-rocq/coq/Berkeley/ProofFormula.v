(** Total decoding of numeric formula codes, without assuming that proof
    parameters are already canonical encodings. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax ConstructorArithmetic ConstructorStreams ProofSearchSyntax.
Import ListNotations.

Inductive fol_formula :=
| FEqual (x y : nat)
| FMember (x y : nat)
| FNeg (p : fol_formula)
| FImp (p q : fol_formula)
| FAll (x : nat) (p : fol_formula).
Fixpoint encode_formula f :=
  match f with
  | FEqual x y => code_eq x y
  | FMember x y => code_mem x y
  | FNeg p => code_neg (encode_formula p)
  | FImp p q => code_imp (encode_formula p) (encode_formula q)
  | FAll x p => code_all x (encode_formula p)
  end.
Fixpoint decode_fuel fuel n :=
  match fuel with
  | 0 => FEqual 0 0
  | S k =>
      let '(body,tag) := uncantor n in
      match tag with
      | 0 => let '(x,y) := uncantor body in FEqual x y
      | 1 => let '(x,y) := uncantor body in FMember x y
      | 2 => let '(p,q) := uncantor body in FImp (decode_fuel k p) (decode_fuel k q)
      | 3 => FNeg (decode_fuel k body)
      | 4 => let '(x,p) := uncantor body in FAll x (decode_fuel k p)
      | _ => FEqual 0 0
      end
  end.
Definition decode_formula n := decode_fuel (S n) n.

Lemma cantor_ge_sum a b : a+b <= cantor a b.
Proof. unfold cantor. pose proof (triangle_ge (a+b)). lia. Qed.
Lemma cantor_body_lt a tag : 0 < tag -> a < cantor a tag.
Proof. pose proof (cantor_ge_sum a tag). lia. Qed.
Lemma uncantor_bounds n a b : uncantor n = (a,b) -> a<=n /\ b<=n.
Proof.
  intro E. pose proof (cantor_uncantor n) as H. rewrite E in H.
  pose proof (cantor_ge_left a b). pose proof (cantor_ge_right a b). lia.
Qed.
Lemma uncantor_positive_body n a tag : uncantor n = (a,tag) -> 0<tag -> a<n.
Proof.
  intros E P. pose proof (cantor_uncantor n) as H. rewrite E in H.
  pose proof (cantor_body_lt a tag P). lia.
Qed.

Theorem decode_fuel_stable n fuel1 fuel2 : n<fuel1 -> n<fuel2 ->
  decode_fuel fuel1 n = decode_fuel fuel2 n.
Proof.
  revert fuel1 fuel2. induction n using lt_wf_ind. intros fuel1 fuel2 B1 B2.
  destruct fuel1 as [|fuel1],fuel2 as [|fuel2]; try lia.
  cbn [decode_fuel]. destruct (uncantor n) as [body tag] eqn:E.
  destruct tag as [|[|[|[|[|tag]]]]]; try reflexivity.
  - destruct (uncantor body) as [p q] eqn:U.
    pose proof (uncantor_bounds _ _ _ U) as [Bp Bq].
    pose proof (uncantor_positive_body _ _ _ E ltac:(lia)) as Bbody.
    f_equal; apply H; lia.
  - pose proof (uncantor_positive_body _ _ _ E ltac:(lia)) as Bbody.
    f_equal; apply H; lia.
  - destruct (uncantor body) as [x p] eqn:U.
    pose proof (uncantor_bounds _ _ _ U) as [Bx Bp].
    pose proof (uncantor_positive_body _ _ _ E ltac:(lia)) as Bbody.
    f_equal; apply H; lia.
Qed.
Lemma decode_fuel_enough fuel n : n<fuel -> decode_fuel fuel n = decode_formula n.
Proof. intro B. unfold decode_formula. apply decode_fuel_stable; lia. Qed.

Lemma decode_equal x y : decode_formula (code_eq x y) = FEqual x y.
Proof. unfold decode_formula,code_eq. cbn [decode_fuel]. now rewrite !uncantor_cantor. Qed.
Lemma decode_member x y : decode_formula (code_mem x y) = FMember x y.
Proof. unfold decode_formula,code_mem. cbn [decode_fuel]. now rewrite !uncantor_cantor. Qed.
Lemma decode_neg p : decode_formula (code_neg p) = FNeg (decode_formula p).
Proof.
  unfold decode_formula at 1. cbn [decode_fuel]. unfold code_neg.
  rewrite uncantor_cantor. f_equal. apply decode_fuel_enough,cantor_body_lt. lia.
Qed.
Lemma decode_imp p q : decode_formula (code_imp p q) = FImp (decode_formula p) (decode_formula q).
Proof.
  unfold decode_formula at 1. cbn [decode_fuel]. unfold code_imp.
  rewrite !uncantor_cantor. f_equal; apply decode_fuel_enough.
  - eapply Nat.le_lt_trans; [apply cantor_ge_left|apply cantor_body_lt; lia].
  - eapply Nat.le_lt_trans; [apply cantor_ge_right|apply cantor_body_lt; lia].
Qed.
Lemma decode_all x p : decode_formula (code_all x p) = FAll x (decode_formula p).
Proof.
  unfold decode_formula at 1. cbn [decode_fuel]. unfold code_all.
  rewrite !uncantor_cantor. f_equal. apply decode_fuel_enough.
  eapply Nat.le_lt_trans; [apply cantor_ge_right|apply cantor_body_lt; lia].
Qed.
Theorem decode_encode_formula f : decode_formula (encode_formula f) = f.
Proof.
  induction f; cbn [encode_formula];
    rewrite ?decode_equal,?decode_member,?decode_neg,?decode_imp,?decode_all;
    congruence.
Qed.

Fixpoint instantiate_formula params f :=
  match f with
  | Atom b x y => (if b then FMember else FEqual) (variable_value params x) (variable_value params y)
  | Neg p => FNeg (instantiate_formula params p)
  | Imp p q => FImp (instantiate_formula params p) (instantiate_formula params q)
  | All x p => FAll (variable_value params x) (instantiate_formula params p)
  | Hole n => decode_formula (params n)
  end.
Theorem decode_formula_code params f :
  decode_formula (formula_code params f) = instantiate_formula params f.
Proof.
  induction f as [b x y|p IH|p IHp q IHq|x p IH|n]; cbn [formula_code instantiate_formula].
  - destruct b; [apply decode_member|apply decode_equal].
  - change (decode_formula (code_neg (formula_code params p)) = FNeg (instantiate_formula params p)).
    now rewrite decode_neg,IH.
  - change (decode_formula (code_imp (formula_code params p) (formula_code params q)) = FImp (instantiate_formula params p) (instantiate_formula params q)).
    now rewrite decode_imp,IHp,IHq.
  - change (decode_formula (code_all (variable_value params x) (formula_code params p)) = FAll (variable_value params x) (instantiate_formula params p)).
    now rewrite decode_all,IH.
  - reflexivity.
Qed.

Print Assumptions decode_fuel_stable.
Print Assumptions decode_equal.
Print Assumptions decode_member.
Print Assumptions decode_neg.
Print Assumptions decode_imp.
Print Assumptions decode_all.
Print Assumptions decode_encode_formula.
Print Assumptions decode_formula_code.
