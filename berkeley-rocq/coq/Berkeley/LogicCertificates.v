(** A small kernel-checked verifier for schema-level Hilbert proof certificates. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
From Berkeley Require Import Syntax TheorySchemas ProofFormula ProofPresentation LogicBridge.
Import ListNotations.
Definition SchemaProvable f := forall vars holes, LogicalProvable (independent_instance vars holes f).
Definition map_parameter (v : list nat) x := match x with V n => V n | P n => P (nth n v n) end.
Fixpoint schema_subst (v : list nat) (h : list formula) f :=
  match f with
  | Atom b x y => Atom b (map_parameter v x) (map_parameter v y)
  | Neg p => Neg (schema_subst v h p)
  | Imp p q => Imp (schema_subst v h p) (schema_subst v h q)
  | All x p => All (map_parameter v x) (schema_subst v h p)
  | Hole n => nth n h (Hole n)
  end.
Lemma parameter_subst_correct v vars x :
  independent_variable vars (map_parameter v x) =
  independent_variable (fun n => vars (nth n v n)) x.
Proof. destruct x; reflexivity. Qed.
Lemma schema_subst_correct v h vars holes f :
  independent_instance vars holes (schema_subst v h f) =
  independent_instance (fun n => vars (nth n v n))
    (fun n => independent_instance vars holes (nth n h (Hole n))) f.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|n]; cbn [schema_subst independent_instance].
  - destruct b; cbn; now rewrite !parameter_subst_correct.
  - now rewrite IH.
  - now rewrite IH,JH.
  - now rewrite parameter_subst_correct,IH.
  - reflexivity.
Qed.
Lemma schema_provable_subst v h f : SchemaProvable f -> SchemaProvable (schema_subst v h f).
Proof. intros H vars holes. rewrite schema_subst_correct. apply H. Qed.
Lemma schema_provable_detach p q : SchemaProvable (Imp p q) -> SchemaProvable p -> SchemaProvable q.
Proof. intros H K vars holes. eapply logical_mp; [apply H|apply K]. Qed.
Lemma schema_provable_gen x p : SchemaProvable p -> SchemaProvable (All (P x) p).
Proof. intros H vars holes. cbn. apply logical_gen,H. Qed.
Lemma schema_axiom i f : nth_error logical_schemas i=Some f -> SchemaProvable f.
Proof. intros H vars holes. eapply logical_axiom; exact H. Qed.
Definition formula_eq_dec : forall a b : formula, {a=b}+{a<>b}.
Proof. decide equality; decide equality; try apply Nat.eq_dec; decide equality. Defined.
Inductive CertificateStep :=
| cert_axiom (i : nat)
| cert_detach (major minor : nat) (mv nv : list nat) (mh nh : list formula)
| cert_gen (premise x : nat).
Definition certificate_step (seen:list formula) (step:CertificateStep) : option formula :=
  match step with
  | cert_axiom i => nth_error logical_schemas i
  | cert_gen premise x => option_map (All (P x)) (nth_error seen premise)
  | cert_detach major minor mv nv mh nh =>
    match nth_error seen major, nth_error seen minor with
    | Some a,Some b =>
      match schema_subst mv mh a with
      | Imp antecedent result =>
         if formula_eq_dec antecedent (schema_subst nv nh b) then Some result else None
      | _ => None
      end
    | _,_ => None
    end
  end.
Lemma schema_lookup seen i f : Forall SchemaProvable seen -> nth_error seen i=Some f -> SchemaProvable f.
Proof. intros H E. apply (proj1 (Forall_forall _ _) H f). now apply nth_error_In in E. Qed.
Theorem certificate_step_sound seen step f : Forall SchemaProvable seen ->
  certificate_step seen step=Some f -> SchemaProvable f.
Proof.
  intros Valid Result. destruct step as [i|major minor mv nv mh nh|premise x].
  - cbn in Result. now apply (schema_axiom i f).
  - cbn in Result. destruct (nth_error seen major) as [a|] eqn:A; try discriminate.
    destruct (nth_error seen minor) as [b|] eqn:B; try discriminate.
    pose proof (schema_provable_subst mv mh a (schema_lookup seen major a Valid A)) as MA.
    pose proof (schema_provable_subst nv nh b (schema_lookup seen minor b Valid B)) as MB.
    destruct (schema_subst mv mh a) as [t x y|p|p q|x p|n] eqn:M; try discriminate.
    destruct (formula_eq_dec p (schema_subst nv nh b)) as [E|E]; try discriminate.
    inversion Result; subst f. rewrite <- E in MB. now apply (schema_provable_detach p q).
  - cbn in Result. destruct (nth_error seen premise) as [p|] eqn:P; try discriminate.
    inversion Result; subst f. apply schema_provable_gen. now apply (schema_lookup seen premise p).
Qed.
Fixpoint certificate_build seen steps :=
  match steps with
  | [] => Some seen
  | step::rest => match certificate_step seen step with
                  | Some f => certificate_build (seen ++ [f]) rest
                  | None => None end
  end.
Theorem certificate_build_sound seen steps result : Forall SchemaProvable seen ->
  certificate_build seen steps=Some result -> Forall SchemaProvable result.
Proof.
  revert seen. induction steps as [|step rest IH]; intros seen Valid E; cbn in E.
  - inversion E; subst result; exact Valid.
  - destruct (certificate_step seen step) as [f|] eqn:F; try discriminate.
    eapply IH; [|exact E]. apply Forall_app. split; [exact Valid|]. constructor.
    + now apply (certificate_step_sound seen step f).
    + constructor.
Qed.
Theorem certificate_sound steps result i f : certificate_build [] steps=Some result ->
  nth_error result i=Some f -> SchemaProvable f.
Proof.
  intros E F. eapply schema_lookup; [|exact F].
  eapply certificate_build_sound; [constructor|exact E].
Qed.
Print Assumptions certificate_sound.
