(** Abstract stack instructions, preserving the exact numeric comparison in
    modus ponens. The connection to the source DAG is a separate theorem. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ConstructorArithmetic ProofSearchSyntax.
Import ListNotations.

Definition theorem_stack := (nat * nat)%type.
Definition execute_instruction (i : instruction) (st : theorem_stack) : theorem_stack :=
  let '(op,a,b,c) := i in let '(t,s) := st in
  match op with
  | 0 => (0,cantor t s)
  | 1 => let '(major,rest) := uncantor s in
         (if Nat.eqb major (code_imp t a) then a else 0,rest)
  | 2 => (code_all a t,s)
  | S (S (S k)) =>
      match instantiated_axiom k a b c with
      | Some f => (f,cantor t s)
      | None => (0,cantor t s)
      end
  end.
Fixpoint execute_program (p : list instruction) (st : theorem_stack) :=
  match p with [] => st | i::rest => execute_program rest (execute_instruction i st) end.
Lemma execute_program_app p q st :
  execute_program (p++q) st = execute_program q (execute_program p st).
Proof. revert st. induction p; intro st; cbn [execute_program app]; auto. Qed.

Inductive StackProvable : nat -> Prop :=
| stack_zero : StackProvable 0
| stack_push t s : NumericProvable t -> StackProvable s -> StackProvable (cantor t s).
Definition AllProvable (st : theorem_stack) := NumericProvable (fst st) /\ StackProvable (snd st).

Lemma stack_unpair_sound s : StackProvable s ->
  let '(t,rest) := uncantor s in NumericProvable t /\ StackProvable rest.
Proof.
  intro H. destruct H.
  - cbn [uncantor unpair_iterations]. split; constructor.
  - rewrite uncantor_cantor. auto.
Qed.
Theorem execute_instruction_sound i st : AllProvable st -> AllProvable (execute_instruction i st).
Proof.
  destruct i as [[[op a] b] c], st as [t s]. intros [T S]. cbn [fst snd] in T,S.
  destruct op as [|[|[|k]]]; cbn [execute_instruction AllProvable fst snd].
  - split; [constructor|now constructor].
  - pose proof (stack_unpair_sound _ S) as H.
    destruct (uncantor s) as [major rest]. destruct H as [M R].
    destruct (Nat.eqb major (code_imp t a)) eqn:E; cbn [AllProvable fst snd]; split; try assumption.
    + apply Nat.eqb_eq in E. subst. eapply numeric_mp; eassumption.
    + constructor.
  - split; [now apply numeric_gen|exact S].
  - destruct (instantiated_axiom k a b c) as [f|] eqn:E; cbn [AllProvable fst snd]; split.
    + eapply numeric_axiom; exact E.
    + now constructor.
    + constructor.
    + now constructor.
Qed.
Theorem execute_program_sound p st : AllProvable st -> AllProvable (execute_program p st).
Proof. revert st. induction p; intros st H; cbn [execute_program]; auto using execute_instruction_sound. Qed.

(** Every derivation has a nonempty postfix instruction program, uniformly
    above any older top and stack. Reused proof lines may be duplicated. *)
Theorem numeric_proof_has_program f : NumericProvable f ->
  exists p, p <> [] /\ forall t s, execute_program p (t,s) = (f,cantor t s).
Proof.
  intro H. induction H as [|i a b c f E|p q Major [pm [NE_M M]] Minor [pn [NE_N N]]|x p P [pp [NE Pp]]].
  - exists [(0,0,0,0)]. split; [discriminate|reflexivity].
  - exists [(S (S (S i)),a,b,c)]. split; [discriminate|].
    intros t s. cbn [execute_program execute_instruction]. now rewrite E.
  - exists (pm ++ pn ++ [(1,q,0,0)]). split.
    + intro E. apply app_eq_nil in E as [E _]. contradiction.
    + intros t s. rewrite !execute_program_app, M, N.
      cbn [execute_program execute_instruction]. rewrite uncantor_cantor,Nat.eqb_refl. reflexivity.
  - exists (pp ++ [(2,x,0,0)]). split.
    + intro E. apply app_eq_nil in E as [E _]. contradiction.
    + intros t s. rewrite execute_program_app,Pp. reflexivity.
Qed.

Print Assumptions execute_instruction_sound.
Print Assumptions execute_program_sound.
Print Assumptions numeric_proof_has_program.
