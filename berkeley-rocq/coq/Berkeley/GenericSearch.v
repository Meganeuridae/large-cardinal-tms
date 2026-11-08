(** The verified fair stack-proof search, parameterized by a total optional
    numeric axiom-instance function. This abstraction supports the repaired
    guarded-axiom presentation without reusing an old machine theorem. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ConstructorArithmetic ProofSearchSyntax.
Import ListNotations.
Section Search.
Variable axiom_instance : nat -> nat -> nat -> nat -> option nat.
Inductive Derivable : nat -> Prop :=
| derive_reflexivity : Derivable 0
| derive_axiom i a b c f : axiom_instance i a b c=Some f -> Derivable f
| derive_mp p q : Derivable (code_imp p q) -> Derivable p -> Derivable q
| derive_gen x p : Derivable p -> Derivable (code_all x p).
Definition GenericInconsistent := Derivable 1.
Definition theorem_stack := (nat * nat)%type.
Definition execute_instruction (i : instruction) (st : theorem_stack) : theorem_stack :=
  let '(op,a,b,c) := i in let '(t,s) := st in
  match op with
  | 0 => (0,cantor t s)
  | 1 => let '(major,rest) := uncantor s in
         (if Nat.eqb major (code_imp t a) then a else 0,rest)
  | 2 => (code_all a t,s)
  | S (S (S k)) =>
      match axiom_instance k a b c with
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
| stack_push t s : Derivable t -> StackProvable s -> StackProvable (cantor t s).
Definition AllProvable (st : theorem_stack) := Derivable (fst st) /\ StackProvable (snd st).

Lemma stack_unpair_sound s : StackProvable s ->
  let '(t,rest) := uncantor s in Derivable t /\ StackProvable rest.
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
    + apply Nat.eqb_eq in E. subst. eapply derive_mp; eassumption.
    + constructor.
  - split; [now apply derive_gen|exact S].
  - destruct (axiom_instance k a b c) as [f|] eqn:E; cbn [AllProvable fst snd]; split.
    + eapply derive_axiom; exact E.
    + now constructor.
    + constructor.
    + now constructor.
Qed.
Theorem execute_program_sound p st : AllProvable st -> AllProvable (execute_program p st).
Proof. revert st. induction p; intros st H; cbn [execute_program]; auto using execute_instruction_sound. Qed.

(** Every derivation has a nonempty postfix instruction program, uniformly
    above any older top and stack. Reused proof lines may be duplicated. *)
Theorem numeric_proof_has_program f : Derivable f ->
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


Record search_state := SearchState {
  pending_program : nat;
  next_program : nat;
  proof_stack : theorem_stack
}.
Definition search_step (s : search_state) :=
  let '(n,next) := match pending_program s with
                  | 0 => (next_program s,S (next_program s))
                  | S n => (n,next_program s) end in
  let '(i,tail) := instruction_decode n in
  SearchState tail next (execute_instruction i (proof_stack s)).
Definition initial_search_state := SearchState 0 0 (0,0).
Inductive SearchRuns : search_state -> search_state -> Prop :=
| search_refl s : SearchRuns s s
| search_next s t : SearchRuns (search_step s) t -> SearchRuns s t.
Definition SearchHalts := exists s,
  SearchRuns initial_search_state s /\ fst (proof_stack s) = 1.

Lemma search_runs_trans a b c : SearchRuns a b -> SearchRuns b c -> SearchRuns a c.
Proof. intro H. induction H; intro R; [exact R|constructor; auto]. Qed.
Lemma search_step_sound s : AllProvable (proof_stack s) ->
  AllProvable (proof_stack (search_step s)).
Proof.
  destruct s as [p n st]. unfold search_step. cbn [pending_program next_program proof_stack].
  destruct p as [|p].
  - destruct (instruction_decode n) as [i tail]; cbn [proof_stack]; apply execute_instruction_sound.
  - destruct (instruction_decode p) as [i tail]; cbn [proof_stack]; apply execute_instruction_sound.
Qed.
Lemma search_runs_sound s t : SearchRuns s t -> AllProvable (proof_stack s) ->
  AllProvable (proof_stack t).
Proof. intro R. induction R; auto using search_step_sound. Qed.
Theorem search_halting_sound : SearchHalts -> GenericInconsistent.
Proof.
  intros [s [Run Halt]]. assert (A : AllProvable (proof_stack initial_search_state)).
  { split; constructor. }
  destruct (search_runs_sound _ _ Run A) as [P _]. rewrite Halt in P. exact P.
Qed.

Lemma search_step_pending i rest next st :
  search_step (SearchState (program_code (i::rest)) next st) =
  SearchState (program_code rest) next (execute_instruction i st).
Proof.
  cbn [program_code search_step pending_program next_program proof_stack].
  now rewrite instruction_decode_encode.
Qed.
Theorem execute_pending_program p next st :
  SearchRuns (SearchState (program_code p) next st)
             (SearchState 0 next (execute_program p st)).
Proof.
  revert st. induction p as [|i p IH]; intro st; [constructor|].
  apply search_next. rewrite search_step_pending. apply IH.
Qed.
Theorem every_pending_program_finishes pending next st :
  exists result, SearchRuns (SearchState pending next st) (SearchState 0 next result).
Proof.
  revert st. induction pending using lt_wf_ind. intros st.
  destruct pending as [|n].
  - exists st. constructor.
  - destruct (instruction_decode n) as [i tail] eqn:E.
    assert (B : tail < S n) by (pose proof (decoded_tail_le _ _ _ E); lia).
    destruct (H tail B (execute_instruction i st)) as [result Run].
    exists result. apply search_next.
    cbn [search_step pending_program next_program proof_stack]. now rewrite E.
Qed.
Lemma next_candidate_finishes next st : exists result,
  SearchRuns (SearchState 0 next st) (SearchState 0 (S next) result).
Proof.
  destruct (instruction_decode next) as [i tail] eqn:E.
  destruct (every_pending_program_finishes tail (S next) (execute_instruction i st))
    as [result Run]. exists result. apply search_next.
  cbn [search_step pending_program next_program proof_stack]. now rewrite E.
Qed.
Theorem every_candidate_reached n : exists st,
  SearchRuns initial_search_state (SearchState 0 n st).
Proof.
  induction n as [|n [st Run]].
  - exists (0,0). constructor.
  - destruct (next_candidate_finishes n st) as [result More].
    exists result. eapply search_runs_trans; eassumption.
Qed.
Theorem any_nonempty_program_runs i rest st :
  SearchRuns (SearchState 0 (instruction_tail i (program_code rest)) st)
    (SearchState 0 (S (instruction_tail i (program_code rest)))
       (execute_program (i::rest) st)).
Proof.
  apply search_next. cbn [search_step pending_program next_program proof_stack].
  rewrite instruction_decode_encode. cbn [execute_program]. apply execute_pending_program.
Qed.
Theorem search_halting_complete : GenericInconsistent -> SearchHalts.
Proof.
  intro P. destruct (numeric_proof_has_program _ P) as [p [NE Runs]].
  destruct p as [|i rest]; [contradiction|].
  destruct (every_candidate_reached (instruction_tail i (program_code rest))) as [st Reach].
  pose proof (any_nonempty_program_runs i rest st) as Execute.
  destruct st as [t s]. rewrite Runs in Execute.
  eexists. split; [eapply search_runs_trans; eassumption|reflexivity].
Qed.
Theorem abstract_search_halting_iff_numeric_inconsistent : SearchHalts <-> GenericInconsistent.
Proof. split; [apply search_halting_sound|apply search_halting_complete]. Qed.


End Search.
Print Assumptions execute_instruction_sound.
Print Assumptions numeric_proof_has_program.
Print Assumptions every_pending_program_finishes.
Print Assumptions every_candidate_reached.
Print Assumptions abstract_search_halting_iff_numeric_inconsistent.
