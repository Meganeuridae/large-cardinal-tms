(** Complete source execution contract for every primitive token actually
    present in the checked grammar's extracted source graph. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorStreams ConstructorGraph ConstructorPush ConstructorFrame ConstructorParam ConstructorCons ConstructorTokensBase ConstructorTokensV ConstructorTokensCompound SourceExecution.
Import ListNotations.

(** The four constructor registers are physical indices 2,3,8,9.  The frame
    freezes every other first-eleven register, and the only parameter tokens
    present in this source use parameter registers 5,6,7 (parameters 1..3). *)
Definition constructor_view (params : nat->nat) (frame : list nat)
    (r : constructor_registers) (rs : list nat) : Prop :=
  11<=length rs /\ nth_error rs 2=Some (top r) /\ nth_error rs 3=Some (stack r) /\
  nth_error rs 8=Some (scratch1 r) /\ nth_error rs 9=Some (scratch2 r) /\
  scratch1 r=0 /\ scratch2 r=0 /\ outside_cons frame rs /\
  (forall n, 1<=n<=3 -> nth_error rs (4+n)=Some (params n)).

Definition TokenRun ctx rs mid result t s : Prop :=
  SourceProgramStep (ctx,rs) mid /\ SourceProgramRuns mid (loop_return ctx,result) /\
  11<=length result /\ nth_error result 2=Some t /\ nth_error result 3=Some s /\
  nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
  outside_cons rs result /\ exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.

Lemma token_run_view params frame initial rs ctx mid result t s :
  constructor_view params frame initial rs -> TokenRun ctx rs mid result t s ->
  constructor_view params frame (CR t s 0 0) result.
Proof.
  intros [L [T [S [X [Y [X0 [Y0 [F P]]]]]]]]
         [First [Run [Len [Top [Stack [Scratch1 [Scratch2 [Change Tail]]]]]]]].
  unfold constructor_view. cbn [top stack scratch1 scratch2].
  repeat split; try assumption.
  - eapply outside_cons_trans; eassumption.
  - intros n N. rewrite (Change (4+n)) by lia. now apply P.
Qed.

Inductive supported_token : nat -> nat -> Prop :=
| supported_eq : supported_token 0 71
| supported_mem : supported_token 1 88
| supported_not : supported_token 2 57
| supported_imp : supported_token 3 44
| supported_all : supported_token 4 61
| supported_par1 : supported_token 9 17
| supported_par2 : supported_token 10 21
| supported_par3 : supported_token 11 51
| supported_variable n : n<=10 -> supported_token (16+n) (variable_root n).

Local Transparent source_token_roots.
Lemma supported_token_complete tok root : In (tok,root) source_token_roots -> supported_token tok root.
Proof.
  intro H. change (In (tok,root)
    ([(0,71);(1,88);(2,57);(3,44);(4,61);(9,17);(10,21);(11,51)] ++
     List.map (fun n => (16+n,variable_root n)) (seq 0 11))) in H.
  apply in_app_iff in H as [Fixed|Vars].
  - cbn [In] in Fixed.
    repeat (destruct Fixed as [E|Fixed]; [inversion E; subst; constructor|]). contradiction.
  - apply in_map_iff in Vars as [n [E I]]. inversion E; subst tok root.
    apply supported_variable. apply in_seq in I. lia.
Qed.

Lemma token_variable_run n ctx rs t s : n<=10 ->
  SourcePrefix source_graph source_root ctx (variable_root n) -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 ->
  nth_error rs 9=Some 0 ->
  exists mid result, TokenRun ctx rs mid result n (cantor t s).
Proof.
  intros H P L T S X Y.
  destruct (source_variable_nonempty n ctx rs t s H P L T S X)
    as [result [mid [First [Run [Len [Top [Stack [Scratch [F [pad Tail]]]]]]]]]].
  assert (Y' : nth_error result 9=Some 0) by (rewrite (F 9) by lia; exact Y).
  exists mid,result. unfold TokenRun. repeat split; try assumption.
  - now apply outside_push_is_cons.
  - now exists pad.
Qed.

Lemma token_parameter_run ctx root p transfer restore rs t s value :
  param_layout root p transfer restore -> SourcePrefix source_graph source_root ctx root ->
  p<11 -> p<>2 -> p<>3 -> p<>8 -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 ->
  nth_error rs 9=Some 0 -> nth_error rs p=Some value ->
  exists mid result, TokenRun ctx rs mid result value (cantor t s).
Proof.
  intros Layout P Hp H2 H3 H8 L T S X Y Param.
  destruct (source_parameter_nonempty ctx root p transfer restore rs t s value
    Layout P Hp H2 H3 H8 L T S X Param)
    as [result [mid [First [Run [Len [Top [Stack [Scratch [F [pad Tail]]]]]]]]]].
  assert (Y' : nth_error result 9=Some 0) by (rewrite (F 9) by lia; exact Y).
  exists mid,result. unfold TokenRun. repeat split; try assumption.
  - now apply outside_push_is_cons.
  - now exists pad.
Qed.

Lemma token_binary_run ctx root tag rs t a rest : binary_layout root tag -> tag<=4 ->
  SourcePrefix source_graph source_root ctx root -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some (cantor a rest) ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists mid result, TokenRun ctx rs mid result (cantor (cantor a t) tag) rest.
Proof.
  intros Layout Tag P L T S X Y.
  destruct (source_binary_nonempty ctx root tag rs t a rest Layout Tag P L T S X Y)
    as [result [mid H]]. exists mid,result. exact H.
Qed.
Lemma token_negation_run ctx rs t s : SourcePrefix source_graph source_root ctx 57 ->
  11<=length rs -> nth_error rs 2=Some t -> nth_error rs 3=Some s ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists mid result, TokenRun ctx rs mid result (cantor t 3) s.
Proof.
  intros P L T S X Y.
  destruct (source_negation_nonempty ctx rs t s P L T S X Y)
    as [result [mid H]]. exists mid,result. exact H.
Qed.

Definition TokenOutput ctx rs final : Prop := exists mid result,
  TokenRun ctx rs mid result (top final) (stack final) /\
  scratch1 final=0 /\ scratch2 final=0.

Lemma supported_token_execution params tok root ctx rs t s final :
  supported_token tok root -> SourcePrefix source_graph source_root ctx root ->
  11<=length rs -> nth_error rs 2=Some t -> nth_error rs 3=Some s ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  (forall n, 1<=n<=3 -> nth_error rs (4+n)=Some(params n)) ->
  token_step params tok (CR t s 0 0)=Some final -> TokenOutput ctx rs final.
Proof.
  intros Supported Prefix Len Top Stack X Y Params Eval.
  destruct Supported as [| | | | | | | |n N].
  all: try (match goal with
  | |- TokenOutput _ _ _ => idtac
  end).
  - destruct (uncantor s) as [a rest] eqn:Un.
    pose proof (cantor_uncantor s) as C. rewrite Un in C. cbn in C. subst s.
    cbn [token_step] in Eval. rewrite source_binary_correct in Eval. inversion Eval; subst final.
    destruct (token_binary_run ctx 71 0 rs t a rest binary_layout_eq ltac:(lia)
      Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - destruct (uncantor s) as [a rest] eqn:Un.
    pose proof (cantor_uncantor s) as C. rewrite Un in C. cbn in C. subst s.
    cbn [token_step] in Eval. rewrite source_binary_correct in Eval. inversion Eval; subst final.
    destruct (token_binary_run ctx 88 1 rs t a rest binary_layout_mem ltac:(lia)
      Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - cbn [token_step] in Eval. rewrite source_negation_correct in Eval. inversion Eval; subst final.
    destruct (token_negation_run ctx rs t s Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - destruct (uncantor s) as [a rest] eqn:Un.
    pose proof (cantor_uncantor s) as C. rewrite Un in C. cbn in C. subst s.
    cbn [token_step] in Eval. rewrite source_binary_correct in Eval. inversion Eval; subst final.
    destruct (token_binary_run ctx 44 2 rs t a rest binary_layout_imp ltac:(lia)
      Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - destruct (uncantor s) as [a rest] eqn:Un.
    pose proof (cantor_uncantor s) as C. rewrite Un in C. cbn in C. subst s.
    cbn [token_step] in Eval. rewrite source_binary_correct in Eval. inversion Eval; subst final.
    destruct (token_binary_run ctx 61 4 rs t a rest binary_layout_all ltac:(lia)
      Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - change (token_step params (8+1) (CR t s 0 0)=Some final) in Eval.
    rewrite parameter_token_correct in Eval by lia. inversion Eval; subst final.
    pose proof (Params 1 ltac:(lia)) as Param. cbn in Param.
    destruct (token_parameter_run ctx 17 5 14 16 rs t s (params 1) param_layout_1 Prefix
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len Top Stack X Y Param) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - change (token_step params (8+2) (CR t s 0 0)=Some final) in Eval.
    rewrite parameter_token_correct in Eval by lia. inversion Eval; subst final.
    pose proof (Params 2 ltac:(lia)) as Param. cbn in Param.
    destruct (token_parameter_run ctx 21 6 18 20 rs t s (params 2) param_layout_2 Prefix
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len Top Stack X Y Param) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - change (token_step params (8+3) (CR t s 0 0)=Some final) in Eval.
    rewrite parameter_token_correct in Eval by lia. inversion Eval; subst final.
    pose proof (Params 3 ltac:(lia)) as Param. cbn in Param.
    destruct (token_parameter_run ctx 51 7 48 50 rs t s (params 3) param_layout_3 Prefix
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len Top Stack X Y Param) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
  - pose proof (variable_token_correct params (V n) t s ltac:(reflexivity)) as E.
    change (token_step params (16+n) (CR t s 0 0)=Some (CR n (cantor t s) 0 0)) in E.
    rewrite E in Eval. inversion Eval; subst final.
    destruct (token_variable_run n ctx rs t s N Prefix Len Top Stack X Y) as [mid [result Run]].
    exists mid,result. cbn [top stack scratch1 scratch2]. auto.
Qed.

Theorem source_token_nonempty params frame tok root ctx rs initial final :
  In (tok,root) source_token_roots -> SourcePrefix source_graph source_root ctx root ->
  constructor_view params frame initial rs -> token_step params tok initial=Some final ->
  exists mid result, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    constructor_view params frame final result /\ outside_cons rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros I Prefix View Eval.
  destruct initial as [t s x y].
  destruct View as [Len [Top [Stack [X [Y [X0 [Y0 [Frame Params]]]]]]]].
  cbn [top stack scratch1 scratch2] in *. subst x y.
  assert (View : constructor_view params frame (CR t s 0 0) rs).
  { unfold constructor_view. cbn [top stack scratch1 scratch2]. repeat split; assumption. }
  pose proof (supported_token_complete tok root I) as Supported.
  destruct (supported_token_execution params tok root ctx rs t s final
    Supported Prefix Len Top Stack X Y Params Eval) as [mid [result [Run [Fx Fy]]]].
  pose proof (token_run_view params frame (CR t s 0 0) rs ctx mid result (top final) (stack final)
    View Run) as FinalView.
  destruct final as [t' s' x' y']. cbn [top stack scratch1 scratch2] in *. subst x' y'.
  destruct Run as [First [Tail [L [T [S [A [B [F Z]]]]]]]].
  exists mid,result. split; [exact First|]. split; [exact Tail|].
  split; [exact FinalView|]. split; assumption.
Qed.
Print Assumptions supported_token_execution.
Print Assumptions source_token_nonempty.
