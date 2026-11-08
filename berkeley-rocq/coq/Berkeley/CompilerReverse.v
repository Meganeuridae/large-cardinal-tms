(** Reverse traversal: every right-moving path in a checked compiled graph
    lifts to a source-pair prefix or to a selected register/halt leaf. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeRegisters RuntimeControl
  RuntimeProgram RuntimeJumps RuntimeTraces CompilerSyntax CompilerProof CompilerData CompilerInstance CompilerEntries.
Import ListNotations.

Inductive SourcePrefix (program : list source_pair) : nat -> list bool -> nat -> Prop :=
| source_prefix_nil i : SourcePrefix program i [] i
| source_prefix_cons i pair b j bits last :
    nth_error program i = Some pair -> select_branch pair b = SNode j ->
    SourcePrefix program j bits last -> SourcePrefix program i (b::bits) last.

Definition right_leaf a q : Prop :=
  match a with
  | SInc i => i < 11 /\ q = inc_entry i
  | SDec i => i < 11 /\ q = dec_entry i
  | SHalt => q = 1385
  | _ => False
  end.

Lemma compiler_has_pair program states i q : compiler_check program states = true ->
  nth_error states i = Some q -> exists pair, nth_error program i = Some pair.
Proof.
  intros C Q. unfold compiler_check in C. apply andb_true_iff in C as [Len _].
  apply Nat.eqb_eq in Len.
  assert (B : i < length program).
  { rewrite Len. apply nth_error_Some. rewrite Q. discriminate. }
  destruct (nth_error program i) as [pair|] eqn:P; [eauto|].
  apply nth_error_None in P. lia.
Qed.

Lemma inc_entry_not_node i : i < 11 -> node (inc_entry i) = false.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma dec_entry_not_node i : i < 11 -> node (dec_entry i) = false.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma halt_not_node : node 1385 = false.
Proof. reflexivity. Qed.

Lemma read_path_from_non_node q bits out : node q = false -> ReadPath q bits out ->
  bits = [] /\ out = q.
Proof.
  intros N P. destruct P; [auto|]. congruence.
Qed.

Theorem read_path_lifts_to_source program states q bits out :
  compiler_check program states = true -> ReadPath q bits out ->
  forall i, nth_error states i = Some q ->
  (exists last, SourcePrefix program i bits last /\ nth_error states last = Some out) \/
  (exists leaf, SourceSelect program i bits leaf /\ right_leaf leaf out).
Proof.
  intros C P. induction P as [q|q b t bits out N T P IH]; intros i Q.
  - left. exists i. split; [constructor|exact Q].
  - destruct (compiler_has_pair _ _ _ _ C Q) as [pair Pair].
    destruct (compiler_pair_checked _ _ _ _ _ C Pair Q) as [_ V].
    specialize (V b).
    destruct (select_branch pair b) as [j|ri|ri| |k|k] eqn:A.
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      destruct (nth_error states j) as [u|] eqn:U; cbn in E; [|discriminate].
      inversion E; subst u. destruct (IH j U) as [[last [S End]]|[leaf [S End]]].
      * left. exists last. split; [econstructor; eassumption|exact End].
      * right. exists leaf. split; [econstructor; eassumption|exact End].
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      destruct (ri <? 11) eqn:B; [|discriminate].
      inversion E; subst t. apply Nat.ltb_lt in B.
      destruct (read_path_from_non_node _ _ _ (inc_entry_not_node _ B) P) as [-> ->].
      right. exists (SInc ri). split.
      * eapply select_leaf; [exact Pair|exact A|reflexivity].
      * cbn [right_leaf]. auto.
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      destruct (ri <? 11) eqn:B; [|discriminate].
      inversion E; subst t. apply Nat.ltb_lt in B.
      destruct (read_path_from_non_node _ _ _ (dec_entry_not_node _ B) P) as [-> ->].
      right. exists (SDec ri). split.
      * eapply select_leaf; [exact Pair|exact A|reflexivity].
      * cbn [right_leaf]. auto.
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      inversion E; subst t.
      destruct (read_path_from_non_node _ _ _ halt_not_node P) as [-> ->].
      right. exists SHalt. split.
      * eapply select_leaf; [exact Pair|exact A|reflexivity].
      * reflexivity.
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      destruct b; cbn in E; [destruct (k <=? 2)|]; discriminate.
    + destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]].
      rewrite T in L. inversion L; subst tr. cbn [compiled_transition] in E.
      destruct b; cbn in E; [destruct k; cbn in E; [|destruct (k <=? 3)]|]; discriminate.
Qed.

Lemma compiler_map_points_to_node i q : nth_error compiler_map i = Some q -> node q = true.
Proof.
  intro Q. destruct (compiler_has_pair _ _ _ _ source_compiler_certificate Q) as [pair P].
  exact (proj1 (compiler_pair_checked _ _ _ _ _ source_compiler_certificate P Q)).
Qed.

Theorem source_read_to_leaf bits q : ReadPath 72 bits q -> node q = false ->
  exists leaf, SourceSelect source_graph source_root bits leaf /\ right_leaf leaf q.
Proof.
  intros P N.
  destruct (read_path_lifts_to_source _ _ _ _ _ source_compiler_certificate P
    _ source_root_maps_to_dispatch) as [[last [S M]]|[leaf [S H]]].
  - pose proof (compiler_map_points_to_node _ _ M). congruence.
  - now exists leaf.
Qed.

Theorem source_read_increment bits i : i < 11 -> ReadPath 72 bits (inc_entry i) ->
  SourceSelect source_graph source_root bits (SInc i).
Proof.
  intros Hi P.
  destruct (source_read_to_leaf _ _ P (inc_entry_not_node _ Hi)) as [leaf [S H]].
  destruct leaf as [j|j|j| |j|j]; cbn [right_leaf] in H; try contradiction.
  - destruct H as [Hj E]. apply inc_entry_injective in E; try assumption. now subst j.
  - destruct H as [Hj E]. exfalso. exact (inc_dec_entries_disjoint i j Hi Hj E).
  - exfalso. apply (inc_entry_not_halt _ Hi). exact H.
Qed.

Theorem source_read_decrement bits i : i < 11 -> ReadPath 72 bits (dec_entry i) ->
  SourceSelect source_graph source_root bits (SDec i).
Proof.
  intros Hi P.
  destruct (source_read_to_leaf _ _ P (dec_entry_not_node _ Hi)) as [leaf [S H]].
  destruct leaf as [j|j|j| |j|j]; cbn [right_leaf] in H; try contradiction.
  - destruct H as [Hj E]. exfalso. apply (inc_dec_entries_disjoint j i Hj Hi). symmetry. exact E.
  - destruct H as [Hj E]. apply dec_entry_injective in E; try assumption. now subst j.
  - exfalso. apply (dec_entry_not_halt _ Hi). exact H.
Qed.

Theorem source_read_halt bits : ReadPath 72 bits 1385 ->
  SourceSelect source_graph source_root bits SHalt.
Proof.
  intro P. destruct (source_read_to_leaf _ _ P halt_not_node) as [leaf [S H]].
  destruct leaf as [j|j|j| |j|j]; cbn [right_leaf] in H; try contradiction; try assumption.
  - destruct H as [Hj E]. exfalso. apply (inc_entry_not_halt _ Hj). symmetry. exact E.
  - destruct H as [Hj E]. exfalso. apply (dec_entry_not_halt _ Hj). symmetry. exact E.
Qed.

Lemma source_prefix_to_leaf program start bits last pair leaf :
  SourcePrefix program start bits last -> nth_error program last = Some pair ->
  select_branch pair true = leaf -> is_leaf leaf = true ->
  SourceSelect program start (bits++[true]) leaf.
Proof.
  intros P. induction P as [i|i pair0 b j bits last A B P IH]; intros Pair Leaf Kind.
  - simpl. eapply select_leaf; eassumption.
  - simpl. eapply select_node; [exact A|exact B|]. now apply IH.
Qed.

Definition left_on_one q :=
  match lookup new_table q true with Some(_,L,_) => true | _ => false end.
Lemma inc_entry_not_left i : i < 11 -> left_on_one (inc_entry i) = false.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma dec_entry_not_left i : i < 11 -> left_on_one (dec_entry i) = false.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma right_leaf_not_left leaf q : right_leaf leaf q -> left_on_one q = false.
Proof.
  destruct leaf as [i|i|i| |i|i]; cbn [right_leaf]; try contradiction.
  - intros [Hi ->]. now apply inc_entry_not_left.
  - intros [Hi ->]. now apply dec_entry_not_left.
  - intros ->. reflexivity.
Qed.

Lemma source_read_left_prefix bits q write target : ReadPath 72 bits q ->
  lookup new_table q true = Some(write,L,target) ->
  exists last, SourcePrefix source_graph source_root bits last /\
    nth_error compiler_map last = Some q.
Proof.
  intros P T. destruct (read_path_lifts_to_source _ _ _ _ _ source_compiler_certificate P
    _ source_root_maps_to_dispatch) as [[last [S M]]|[leaf [S H]]]; [eauto|].
  pose proof (right_leaf_not_left _ _ H) as E. unfold left_on_one in E. rewrite T in E. discriminate.
Qed.

Theorem source_read_continue bits q k : ReadPath 72 bits q ->
  lookup new_table q true = Some(false,L,continue_state k) -> k <= 3 ->
  SourceSelect source_graph source_root (bits++[true]) (SContinue (S k)).
Proof.
  intros P T K.
  destruct (source_read_left_prefix _ _ _ _ P T) as [i [Prefix Q]].
  destruct (compiler_has_pair _ _ _ _ source_compiler_certificate Q) as [pair Pair].
  destruct (compiler_pair_checked _ _ _ _ _ source_compiler_certificate Pair Q) as [_ V].
  specialize (V true).
  destruct (select_branch pair true) as [j|ri|ri| |level|level] eqn:A.
  all: destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]]; rewrite T in L;
       inversion L; subst tr; cbn [compiled_transition] in E.
  - destruct (nth_error compiler_map j); discriminate.
  - destruct (ri <? 11); discriminate.
  - destruct (ri <? 11); discriminate.
  - discriminate.
  - destruct (level <=? 2) eqn:B; [|discriminate].
    inversion E. apply Nat.leb_le in B.
    exfalso. eapply (continue_break_disjoint k level); eauto.
  - destruct level as [|level]; cbn in E; [discriminate|].
    destruct (level <=? 3) eqn:B; cbn in E; [|discriminate].
    inversion E. apply Nat.leb_le in B.
    assert (level = k) by (eapply continue_state_injective; eauto).
    subst level. eapply source_prefix_to_leaf; [exact Prefix|exact Pair|exact A|reflexivity].
Qed.

Theorem source_read_break bits q k : ReadPath 72 bits q ->
  lookup new_table q true = Some(false,L,break_state k) -> k <= 2 ->
  SourceSelect source_graph source_root (bits++[true]) (SBreak k).
Proof.
  intros P T K.
  destruct (source_read_left_prefix _ _ _ _ P T) as [i [Prefix Q]].
  destruct (compiler_has_pair _ _ _ _ source_compiler_certificate Q) as [pair Pair].
  destruct (compiler_pair_checked _ _ _ _ _ source_compiler_certificate Pair Q) as [_ V].
  specialize (V true).
  destruct (select_branch pair true) as [j|ri|ri| |level|level] eqn:A.
  all: destruct (compiler_edge_checked _ _ _ _ V) as [tr [E L]]; rewrite T in L;
       inversion L; subst tr; cbn [compiled_transition] in E.
  - destruct (nth_error compiler_map j); discriminate.
  - destruct (ri <? 11); discriminate.
  - destruct (ri <? 11); discriminate.
  - discriminate.
  - destruct (level <=? 2) eqn:B; [|discriminate].
    inversion E. apply Nat.leb_le in B.
    assert (level = k) by (eapply break_state_injective; eauto).
    subst level. eapply source_prefix_to_leaf; [exact Prefix|exact Pair|exact A|reflexivity].
  - destruct level as [|level]; cbn in E; [discriminate|].
    destruct (level <=? 3) eqn:B; cbn in E; [|discriminate].
    inversion E. apply Nat.leb_le in B.
    exfalso. eapply (continue_break_disjoint level k); eauto.
Qed.

Theorem ir_step_implies_source a b : IRStep a b -> SourceStep a b.
Proof.
  intro H. destruct H.
  - eapply source_increment; [eapply source_read_increment; eassumption|exact H1].
  - eapply source_decrement_zero; [eapply source_read_decrement; eassumption|exact H1].
  - eapply source_decrement_positive; [eapply source_read_decrement; eassumption|exact H1].
  - eapply source_continue; [eapply source_read_continue; eassumption|exact H2].
  - eapply source_break; [eapply source_read_break; eassumption|exact H2].
Qed.

Theorem source_ir_step_equivalence a b : SourceStep a b <-> IRStep a b.
Proof. split; [apply source_step_implies_ir|apply ir_step_implies_source]. Qed.
Theorem source_ir_terminal_equivalence s : SourceTerminal s <-> IRTerminal s.
Proof.
  unfold SourceTerminal, IRTerminal. split.
  - intro S. now apply source_program_selection in S.
  - apply source_read_halt.
Qed.
Theorem source_ir_runs_equivalence a b : SourceRuns a b <-> IRRuns a b.
Proof.
  split; [apply source_trace_implies_ir|].
  intro R. induction R as [s|s t u Step Runs IH]; [constructor|].
  eapply source_next with (t:=t); [apply ir_step_implies_source; exact Step|exact IH].
Qed.
Theorem source_ir_halting_equivalence s : SourceHalts s <-> IRHalts s.
Proof.
  unfold SourceHalts, IRHalts. split; intros [t [R H]]; exists t; split.
  - now apply source_ir_runs_equivalence.
  - now apply source_ir_terminal_equivalence.
  - now apply source_ir_runs_equivalence.
  - now apply source_ir_terminal_equivalence.
Qed.

Print Assumptions read_path_lifts_to_source.
Print Assumptions source_read_to_leaf.
Print Assumptions source_read_increment.
Print Assumptions source_read_decrement.
Print Assumptions source_read_halt.
Print Assumptions source_read_continue.
Print Assumptions source_read_break.
Print Assumptions source_ir_step_equivalence.
Print Assumptions source_ir_halting_equivalence.
