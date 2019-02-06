Require Import lib.LibTacticsMin.
Require Import bbv.ZLib.
Require Import riscv.util.Monads. Require Import riscv.util.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.RiscvMachine.
Require Import riscv.Execute.
Require Import riscv.Run.
Require Import riscv.Memory.
Require Import riscv.util.PowerFunc.
Require Import riscv.util.ListLib.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.InstructionCoercions.
Require Import riscv.Primitives.
Require Import Coq.micromega.Lia.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.
Require Import riscv.util.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.
Require Import riscv.MkMachineWidth.
Require Import riscv.runsToNonDet.
Require Import compiler.Rem4.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import compiler.Simp.
Require Import compiler.SimplWordExpr.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section TODO.
  Context {K V: Type}.
  Context {M: map.map K V}.
  Axiom put_put_same: forall k v1 v2 m, map.put (map.put m k v1) k v2 = map.put m k v2.
End TODO.


Local Set Refine Instance Mode.

Definition TODO{T: Type}: T. Admitted.

Module Import FlatToRiscv.
  Export FlatToRiscvDef.FlatToRiscvDef.

  Class parameters := {
    def_params :> FlatToRiscvDef.parameters;

    W :> Words;

    locals :> map.map Register word;
    locals_ok :> map.ok locals;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;
    actname_eq_dec :> DecidableEq actname;

    iset := if width =? 32 then RV32IM else RV64IM;

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PR :> Primitives actname M;

    trace := list (mem * Syntax.actname * list word * (mem * list word));
    ext_spec : trace -> mem -> Syntax.actname -> list word -> (mem -> list word -> Prop) -> Prop;

    (* these two instances are needed to define compile_ext_call_correct below *)

    syntax_params: Syntax.parameters := {|
      Syntax.varname := Register;
      Syntax.funname := Empty_set;
      Syntax.actname := actname;
    |};

    env :> map.map Syntax.funname (list Syntax.varname * list Syntax.varname * stmt);
    env_ok: map.ok env;

    FlatImp_params: FlatImp.parameters := {|
      FlatImp.syntax_params := syntax_params;
      FlatImp.ext_spec := ext_spec;
      FlatImp.max_ext_call_code_size := max_ext_call_code_size;
      FlatImp.max_ext_call_code_size_nonneg a := TODO;
    |};

    Machine := @RiscvMachine Register W _ mem actname;

    (* An abstract predicate on the low-level state, which can be chosen by authors of
       extensions. The compiler will ensure that this guarantee holds before each external
       call. *)
    ext_guarantee: Machine -> Prop;

    (* For authors of extensions, a freely choosable ext_guarantee sounds too good to be true!
       And indeed, there are two restrictions:
       The first restriction is that ext_guarantee needs to be preservable for the compiler: *)
    ext_guarantee_preservable: forall (m1 m2: Machine),
        ext_guarantee m1 ->
        (forall a: word, map.get m1.(getMem) a = None <-> map.get m2.(getMem) a = None) ->
        m1.(getLog) = m2.(getLog) ->
        ext_guarantee m2;

    (* And the second restriction is part of the correctness requirement for compilation of
       external calls: Every compiled external call has to preserve ext_guarantee *)
    compile_ext_call_correct: forall (initialL: Machine) action postH newPc insts
        (argvars resvars: list Register) initialMH R,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.mul (word.of_Z 4) (word.of_Z (Zlength insts))) ->
      Forall valid_register argvars ->
      Forall valid_register resvars ->
      (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      ext_guarantee initialL ->
      exec map.empty (@SInteract (@FlatImp.syntax_params FlatImp_params) resvars action argvars)
           initialL.(getLog) initialMH initialL.(getRegs) initialL.(getMetrics) postH ->
      runsTo (mcomp_sat (run1 iset)) initialL
             (fun finalL =>
                  (* external calls can't modify the memory or metrics for now *)
                  postH finalL.(getLog) initialMH finalL.(getRegs) finalL.(getMetrics) /\
                  finalL.(getPc) = newPc /\
                  finalL.(getNextPc) = add newPc (ZToReg 4) /\
                  (program initialL.(getPc) insts * eq initialMH * R)%sep finalL.(getMem) /\
                  ext_guarantee finalL);

    (* bitwidth-specific: *)
    go_load: forall sz x a (addr v: word) initialL post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) addr = Some v ->
      mcomp_sat (f tt) (withRegs (map.put initialL.(getRegs) x v) initialL) post ->
      mcomp_sat (Bind (execute (compile_load iset sz x a 0)) f) initialL post;

    go_store: forall sz x a (addr v: word) initialL m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) addr v = Some m' ->
      mcomp_sat (f tt) (withMem m' initialL) post ->
      mcomp_sat (Bind (execute (compile_store iset sz a x 0)) f) initialL post;

  }.

End FlatToRiscv.

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscv.parameters}.

  Notation var := Z (only parsing).

  Definition trace := list (LogItem actname).

  Local Notation RiscvMachineL := (RiscvMachine Register actname).

  Ltac state_calc0 := map_solver locals_ok.

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: word) {T: Type} (thenVal elseVal: T),
    (if ltu (sub y  z) (fromImm 1) then thenVal else elseVal) =
    (if reg_eqb y z        then thenVal else elseVal).
  Proof. (*
    intros. destruct (weq y z).
    - subst z. unfold wminus. rewrite wminus_inv.
      destruct (wlt_dec (wzero wXLEN) $1); [reflexivity|].
      change (wzero wXLEN) with (natToWord wXLEN 0) in n. unfold wlt in n.
      exfalso. apply n.
      do 2 rewrite wordToN_nat. rewrite roundTrip_0.
      clear.
      destruct wXLEN as [|w1] eqn: E.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1. simpl. constructor.
    - destruct (@wlt_dec wXLEN (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      clear -E.
      destruct wXLEN as [|w1] eqn: F.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1 in E.
        simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
        apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
        apply wordToNat_inj in E.
        exact E.
  Qed.
*)
  Admitted.

  (*
  Lemma wlshift_bitSlice_plus: forall (sz1 sz2: Z) v,
      (0 <= sz1)%Z ->
      (0 <= sz2)%Z ->
      wlshift (ZToWord wXLEN (bitSlice v sz1 (sz1 + sz2))) (Z.to_nat sz1)
      ^+ ZToWord wXLEN (bitSlice v 0 sz1)
      = ZToWord wXLEN (bitSlice v 0 (sz1 + sz2)).
  Proof.
    intros. rewrite wlshift_alt.
    rewrite wlshift_mul_Zpow2 by assumption.
    rewrite <- ZToWord_mult.
    rewrite <- ZToWord_plus.
    f_equal.
    apply bitSlice_split; assumption.
  Qed.
  *)

  (*
  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq var x x0)", which is annoying. *)
  Notation var := var.
  Existing Instance eq_name_dec.
   *)

  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Arguments Z.mul: simpl never.
  Arguments Z.add: simpl never.
  Arguments run1: simpl never.

  Lemma nth_error_nil_Some: forall {A} i (a: A), nth_error nil i = Some a -> False.
  Proof.
    intros. destruct i; simpl in *; discriminate.
  Qed.

  Ltac ensure_is_nat_rel R :=
    match R with
    | ?P /\ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | ?P \/ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | @eq nat _ _  => idtac (* can't use %nat here because = is polymorphic *)
    | (_ <  _)%nat => idtac
    | (_ <= _)%nat => idtac
    | (_ >  _)%nat => idtac
    | (_ >= _)%nat => idtac
    end.

  Lemma pow2_wXLEN_4: 4 < 2 ^ XLEN.
  Proof.
    unfold XLEN, MachineWidth_XLEN.
    pose proof (@word.width_pos _ _ word_ok).
    pose proof (Z.pow_gt_1 2 width).
    (* TODO doesn't hold, if we want this we'll have to add a stronger bound to Words,
       or somewhere else *)
  Admitted.

  Ltac nat_rel_with_words_pre :=
    match goal with
    | |- ?P => ensure_is_nat_rel P
    end(*;
    repeat match goal with
           | IsMem: Memory.Memory ?M _, m: ?M |- _ =>
             unique pose proof (@Memory.memSize_bound M _ IsMem m)
           end;
    pose proof pow2_wXLEN_4;
    rewrite? wordToNat_wplus in *;
    rewrite? wordToNat_natToWord_eqn in * *).

  Ltac nat_rel_with_words :=
    nat_rel_with_words_pre(*;
    nat_div_mod_to_quot_rem;
    nia *).

  Definition runsTo: RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop :=
    runsTo (mcomp_sat (run1 iset)).

  Lemma one_step: forall initialL P,
      mcomp_sat (run1 iset) initialL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros.
    apply runsToDone. assumption.
  Qed.

  Lemma det_step: forall initialL midL P,
      mcomp_sat (run1 iset) initialL (eq midL) ->
      runsTo midL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros. subst.
    assumption.
  Qed.

  Ltac simpl_run1 :=
    cbv [run1 (*execState*) OStateNDOperations.put OStateNDOperations.get
         Return Bind State_Monad OStateND_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         getRegs getPc getNextPc getMem getLog
         getPC setPC getRegister setRegister].

  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        clear -H;
        unfold stmt_not_too_big in *;
        change (2 ^ 9)%Z with 512%Z in *;
        simpl stmt_size in H;
        repeat match goal with
               | s: stmt |- _ => unique pose proof (stmt_size_pos s)
               end;
        lia
    end.

  (* Needed because simpl will unfold (4 * ...) which is unreadable *)
  Local Ltac simpl_pow2 := idtac. (*
    repeat match goal with
    | |- context [1 + ?a] => change (1 + a) with (S a)
    | |- context [pow2 (S ?a)] => change (pow2 (S a)) with (2 * pow2 a)
    | |- context [pow2 0] => change (pow2 0) with 1
    end.
*)

  Ltac simpl_RiscvMachine_get_set := simpl in *. (* TODO is this enough? *)

  Ltac destruct_RiscvMachine_0 m :=
    let t := type of m in
    unify t RiscvMachine;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let e := fresh m "_eh" in
    let me := fresh m "_mem" in
    destruct m as [ [r p n e] me ];
    simpl_RiscvMachine_get_set.

  Ltac destruct_RiscvMachine m :=
    let t := type of m in
    unify t RiscvMachineL;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let l := fresh m "_log" in
    destruct m as [r p n me l];
    simpl_RiscvMachine_get_set.

  Arguments Z.modulo : simpl never.

  Hint Unfold
       Program.getRegister
       Program.setRegister
       Program.loadByte
       Program.loadHalf
       Program.loadWord
       Program.loadDouble
       Program.storeByte
       Program.storeHalf
       Program.storeWord
       Program.storeDouble
       Program.getPC
       Program.setPC
       Program.step
       Program.raiseException
    : unf_Program_methods.

(*
  Ltac prove_go_lemma :=
    intros;
    unfold valid_register, computation_satisfies in *;
    autounfold with unf_Program_methods in *;
    unfold IsRiscvMachineL in *;
    unfold valid_register, Register0,
           liftLoad, liftStore, logEvent in *;
    repeat match goal with
           | |- _ => reflexivity
           | |- _ => progress (subst)
           | |- _ => solve [exfalso; lia]
           | |- _ => discriminate
           | |- _ => assumption
           | |- _ => rewrite associativity
           | |- _ => rewrite OStateNDOperations.Bind_get
           | |- _ => rewrite OStateNDOperations.Bind_put
           | |- _ => rewrite left_identity
           | |- context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn: E
           | _: context [if ?x then _ else _] |- _ => let E := fresh "E" in destruct x eqn: E
           end.
*)

  Ltac sidecondition_less_safe := eassumption || reflexivity || idtac.

  (*
  Notation K := Z.
  Notation V := mword.
  *)

  (* only strictly needed if we want to export the goal into a map_solver-only environment,
     but might result in a speed up if used anyways *)
  Ltac prepare_for_map_solver :=
    repeat match goal with
             | IH: forall (s : stmt), _ |- _ => clear IH
             | H: context [FlatImp.modVars ?var ?func ?s] |- _ =>
               let n := fresh "mv" s in
               forget (FlatImp.modVars var func s) as n
         (*  | H: Memory.read_mem _ _ = _ |- _ => clear H *)
             | H: ?P |- _ =>
               let h := head_of_app P in
               match h with
               | @stmt_not_too_big => clear H
               | @valid_register => clear H
               | @valid_registers => clear H
               | @divisibleBy4 => clear H
               end
             | H: @eq ?T _ _ |- _ =>
               match T with
            (* | option Semantics.word => don't clear because we have maps of Semantics.word *)
           (*  | option (map Z word * Memory.mem) => clear H *)
               | option mem => clear H
               | list _ => clear H
               | nat => clear H
               end
           end;
    repeat match goal with
           | H: ?P |- _ =>
             progress
               tryif (let T := type of P in unify T Prop)
               then revert H
               else (match P with
                     | _ => clear H
                     end)
           end;
    repeat match goal with
           | x: ?T |- _ =>
             lazymatch T with
             | MachineWidth _  => fail
             | DecidableEq _ => fail
             | _ => revert x
             end
           end.

  Ltac state_calc_with_logging :=
    prepare_for_map_solver;
    idtac "map_solver goal:";
    match goal with
    | |- ?G => idtac G
    end;
    time state_calc0.

  Ltac state_calc_with_timing :=
    prepare_for_map_solver;
    time state_calc0.

  Ltac state_calc_without_logging :=
    prepare_for_map_solver;
    state_calc0.

  Ltac state_calc := state_calc_without_logging.

(*
  Hint Rewrite
      (@associativity  _ (OStateND_Monad RiscvMachine))
      (@left_identity  _ (OStateND_Monad RiscvMachine))
      (@right_identity _ (OStateND_Monad RiscvMachine))
      (@Bind_getRegister _ _ _ _ _ _ _)
      (@Bind_getRegister0 _ _ _ _ _ _ _)
      (@Bind_setRegister _ _ _ _ _ _ _)
      (@Bind_setRegister0 _ _ _ _ _ _ _)
      (@Bind_getPC _ _ _ _ _ _ _)
      (@Bind_setPC _ _ _ _ _ _ _)
  using assumption : rew_get_set_Register.

  Ltac do_get_set_Register := autorewrite with rew_get_set_Register.
*)

  (* requires destructed RiscvMachine and containsProgram *)
  Ltac fetch_inst :=
    eapply go_fetch_inst; [reflexivity|simpl (*; solve_containsProgram *)|].

  Ltac rewrite_reg_value :=
    match goal with
    | |- context [get    _ _] => idtac
    | _ => fail 1 "wrong shape of goal"
    end. (*;
    let G1 := fresh "G1" in
    match goal with
    | G2: get ?st2 ?x = ?v, E: map.extends ?st1 ?st2 |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
      progress change gg with gg';
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    | G2: get ?st2 ?x = ?v, E: map.extends ?st1 ?st2 |- context [?gg'] =>
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    end;
    rewrite G1;
    clear G1. *)

  Ltac rewrite_getReg := idtac. (*
    match goal with
    | |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end. *)

  Ltac rewrite_setReg := idtac. (*
    match goal with
    | |- context [@setReg ?RF ?R ?V ?TC ?st1 ?x ?v] =>
      let gg := constr:(@setReg RF R V TC st1 x v) in
      let gg' := eval unfold setReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end. *)

  Ltac solve_valid_registers :=
    match goal with
    | |- valid_registers _ => solve [simpl; auto]
    end.

  Lemma add_to_instsBefore: forall (before insts1 insts2 after: list Instruction),
      before ++ (insts1 ++ insts2) ++ after = (before ++ insts1) ++ insts2 ++ after.
  Proof. intros. rewrite <-? app_assoc. reflexivity. Qed.

  Lemma add_to_instsAfter: forall (before insts1 insts2 after: list Instruction),
      before ++ (insts1 ++ insts2) ++ after = before ++ insts1 ++ (insts2 ++ after).
  Proof. intros. rewrite <-? app_assoc. reflexivity. Qed.

  (* Solves an equality of the form
        before ++ insts ++ after = evarForBefore ++ subseqOfInsts ++ evarForAfter
     instantiating evarForBefore and evarForAfter appropriately.
     Works by first shoveling instructions from "insts" into "before" until "subseqOfInsts"
     is found, and then shoveling the remaining instructions from "insts" into "after". *)
  Ltac solve_imem :=
    repeat match goal with
           | H: _ |- _ => clear H
           end;
    let targetInsts := fresh "targetInsts" in
    lazymatch goal with
    | |- ?lhs = _ ++ ?insts ++ _ =>
      match lhs with
      | context [insts] => remember insts as targetInsts
      end
    end;
    repeat match goal with
           | |- context [?h :: ?t] =>
             tryif (unify t [[]])
             then fail
             else (change (h :: t) with ([h] ++ t))
           end;
    repeat match goal with
           | |- ?before ++ (targetInsts ++ ?insts2) ++ ?after = _ => fail 1 (* success/quit loop *)
           | |- ?before ++ (?insts1 ++ ?insts2) ++ ?after = _ =>
             rewrite (add_to_instsBefore before insts1 insts2 after)
           end;
    repeat match goal with
           | |- ?before ++ (?insts1 ++ ?insts2) ++ ?after = _ =>
             rewrite (add_to_instsAfter before insts1 insts2 after)
           end;
    subst targetInsts;
    reflexivity.

  Lemma write_mem_preserves_mem_accessibility:
    forall {initialMem finalMem: mem} {a0: word} {w: w32},
      Memory.storeWord initialMem a0 w = Some finalMem ->
      forall a, Memory.loadWord initialMem a = None <-> Memory.loadWord finalMem a = None.
  Proof. Admitted. (*
    intros. unfold Memory.write_mem in *.
    destruct_one_match_hyp; [|discriminate].
    inversions H.
    unfold Memory.read_mem in *.
    split; intros.
    - repeat destruct_one_match. subst.
      + apply reg_eqb_true in E1. subst. rewrite E0 in E. rewrite E in H. discriminate.
      + assumption.
      + reflexivity.
    - repeat destruct_one_match_hyp; subst; reflexivity || discriminate || assumption.
  Qed. *)

  (*
  Lemma mem_accessibility_trans:
    forall {initialMem middleMem finalMem: Memory.mem} {a: word},
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a middleMem = None) ->
      (Memory.read_mem a middleMem  = None <-> Memory.read_mem a finalMem  = None) ->
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem  = None).
  Proof. intros. tauto. Qed.

  Lemma eval_stmt_preserves_mem_accessibility:  forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: stmt} {initialRegs finalRegs: state},
      eval_stmt _ _ empty_map fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
      forall a, Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem = None.
  Proof.
    induction fuel; intros; try (simpl in *; discriminate).
    destruct s; simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      inversions H;
      try reflexivity.
    - eauto using write_mem_preserves_mem_accessibility.
    - destruct_one_match_hyp; eauto.
    - destruct p.
      repeat (destruct_one_match_hyp; try discriminate).
      + inversions H1. eauto.
      + eapply mem_accessibility_trans; [ eauto | ].
        eapply mem_accessibility_trans; [ eauto | ].
        eauto.
    - destruct p.
      eapply mem_accessibility_trans; eauto.
    - rewrite empty_is_empty in E. discriminate E.
  Qed.

  Lemma eval_stmt_preserves_mem_inaccessible: forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: stmt} {initialRegs finalRegs: state},
      eval_stmt _ _ empty_map fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
      forall start len,
        mem_inaccessible initialMem start len -> mem_inaccessible finalMem start len.
  Proof.
    unfold mem_inaccessible. intros.
    destruct (Memory.read_mem a initialMem) eqn: E.
    - eapply H0. exact E.
    - pose proof (eval_stmt_preserves_mem_accessibility H a) as P.
      destruct P as [P _]. specialize (P E). exfalso. congruence.
  Qed.
  *)

  Ltac prove_remu_four_zero :=
    match goal with
    | |- remu _ (ZToReg 4) = ZToReg 0 => idtac
    | |- ZToReg 0 = remu _ (ZToReg 4) => symmetry
    | _ => fail 1 "wrong shape of goal"
    end;
    rewrite <-? (Z.mul_comm 4);
    autorewrite with rew_ZToReg_morphism;
    repeat (apply remu_four_zero_distrib_plus);
    rewrite? remu_four_undo;
    rewrite? remu_four_four;
    repeat match goal with
           | H: divisibleBy4 _ |- _ => apply divisibleBy4_remu40 in H; rewrite H
           end;
    ring.

(*
  Ltac solve_mem_inaccessible :=
    eapply eval_stmt_preserves_mem_inaccessible; [|eassumption];
    try eassumption;
    let Eq := fresh "Eq" in
    match goal with
    | E1: eval_stmt _ _ ?env ?f ?r1 ?m1 ?s1 = Some (?r2, ?m2),
      E2: eval_stmt _ _ ?env ?f ?r2 ?m2 ?s2 = Some (?r3, ?m3)
      |-   eval_stmt _ _ ?env _ _ ?m1 _ = Some (_, ?m3)
      => assert (eval_stmt _ _ env (S f) r1 m1 (SSeq s1 s2) = Some (r3, m3)) as Eq
          by (simpl; rewrite E1; exact E2); exact Eq
    end.

  Ltac spec_IH originalIH IH stmt1 :=
    pose proof originalIH as IH;
    match goal with
    | |- runsTo ?st _ => specialize IH with (initialL := st); simpl in IH
    end;
    specialize IH with (s := stmt1);
    specializes IH;
    first
      [ reflexivity
      | solve_imem
      | solve_stmt_not_too_big
      | solve_valid_registers
      | solve_containsProgram
      | solve_word_eq
      | eassumption
      | solve_mem_inaccessible
      | idtac ].
  *)

  Ltac simpl_remu4_test :=
    match goal with
    | |- context [reg_eqb ?r ?expectZero] =>
      match expectZero with
      | ZToReg 0 => idtac
      end;
      match r with
      | remu ?a (ZToReg 4) => replace r with expectZero by prove_remu_four_zero
      end
    end;
    rewrite word.eqb_eq by reflexivity;
    simpl.

  Hint Rewrite word.eqb_ne word.eqb_eq using congruence : rew_reg_eqb.

  Hint Rewrite
      elim_then_true_else_false
      (@left_identity M MM)
      @map.get_put_same
      @put_put_same
  : rew_run1step.

  Ltac simpl_bools :=
    repeat match goal with
           | H : ?x = false |- _ =>
             progress rewrite H in *
           | H : ?x = true |- _ =>
             progress rewrite H in *
           | |- context [negb true] => progress unfold negb
           | |- context [negb false] => progress unfold negb
           | H : negb ?x = true |- _ =>
             let H' := fresh in
             assert (x = false) as H' by (eapply negb_true_iff; eauto);
             clear H
           | H : negb ?x = false |- _ =>
             let H' := fresh in
             assert (x = true) as H' by (eapply negb_false_iff; eauto);
             clear H
           end.

  Ltac destruct_everything :=
    destruct_products;
    try destruct_pair_eqs;
    destruct_conjs;
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end;
    subst.

  Ltac run1step''' :=
    repeat (
        autorewrite with
            rew_get_set_Register
            rew_RiscvMachine_get_set
            rew_reg_eqb
            rew_run1step ||
        simpl_bools ||
        rewrite_getReg ||
        rewrite_setReg ||
        simpl_remu4_test ||
        rewrite_reg_value).

  Ltac run1step'' :=
    fetch_inst;
    autounfold with unf_pseudo in *;
    cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
    run1step'''.

  Ltac run1step' :=
    (eapply runsToStep; simpl in *; subst * ); [ run1step'' | ].

  Ltac run1step :=
    run1step'; do 2 intro; subst.

  Ltac run1done :=
    apply runsToDone;
    simpl in *;
    repeat split;
    first
      [ eassumption
      | solve_word_eq (@word_ok (@W p))
      | seplog
      | idtac ].

(*
  Ltac IH_done IH :=
    eapply runsToSatisfying_imp; [ exact IH | ];
    subst;
    clear;
    simpl;
    intros;
    destruct_products;
    repeat match goal with
           | |- _ /\ _ => split
           end;
    try assumption;
    try match goal with
        | H: ?m.(core).(pc) = _ |- ?m.(core).(pc) = _ => rewrite H
        end;
    solve_word_eq.
*)

  Arguments LittleEndian.combine: simpl never.

  Definition load_lit_semantics(v: Z): word :=
    add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add
      (ZToReg 0)
      (ZToReg (bitSlice v (7 * 8) (8 * 8)))) 8)
      (ZToReg (bitSlice v (6 * 8) (7 * 8)))) 8)
      (ZToReg (bitSlice v (5 * 8) (6 * 8)))) 8)
      (ZToReg (bitSlice v (4 * 8) (5 * 8)))) 8)
      (ZToReg (bitSlice v (3 * 8) (4 * 8)))) 8)
      (ZToReg (bitSlice v (2 * 8) (3 * 8)))) 8)
      (ZToReg (bitSlice v (1 * 8) (2 * 8)))) 8)
      (ZToReg (bitSlice v (0 * 8) (1 * 8))).

  Lemma compile_lit_correct: forall v: Z,
      load_lit_semantics v = ZToReg v.
  Proof using .
  Admitted.

  Lemma compile_lit_correct_full: forall initialL post x v R,
      initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
      let insts := compile_stmt iset (SLit x v) in
      let d := mul (ZToReg 4) (ZToReg (Zlength insts)) in
      (program initialL.(getPc) insts * R)%sep initialL.(getMem) ->
      valid_register x ->
      runsTo (withRegs   (map.put initialL.(getRegs) x (ZToReg v))
             (withPc     (add initialL.(getPc) d)
             (withNextPc (add initialL.(getNextPc) d)
                         initialL)))
             post ->
      runsTo initialL post.
  Proof.
    intros. subst insts d.
    (*
    unfold compile_stmt, compile_lit, compile_lit_rec in *.
    destruct_everything; simpl in *.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    Time run1step.
    match goal with
    | R: runsTo ?m post |- runsToNonDet.runsTo _ _ ?m' post =>
      replace m' with m; [exact R|]
    end.
    f_equal; try solve_word_eq.
    f_equal. symmetry. apply compile_lit_correct.
  Qed.
  *)
  Admitted.

  Existing Instance FlatToRiscv.syntax_params.
  Existing Instance FlatToRiscv.FlatImp_params.

  Definition eval_stmt := exec map.empty.

  Lemma seplog_subst_eq: forall {A B R: mem -> Prop} {mL mH: mem},
      A mL ->
      iff1 A (R * eq mH)%sep ->
      B mH ->
      (B * R)%sep mL.
  Proof.
  Admitted.

  Lemma doesSupportM: supportsM iset = true.
  Proof.
    unfold iset. destruct_one_match; reflexivity.
  Qed.

  (* note: before we can apply this lemma, we have to extend the FlatImp execution from a
     high-level memory to the low-level memory (which adds the instruction memory and
     possibly more later).
     Doing this could also be done at ExprImp level, and will be a separate proof.
     A similar proof will add one more precondition to ext_spec for MMIO to say that
     the MMIO action does not happen on physical memory (and this has to include the
     whole memory).
     In order to prove compile_ext_call_correct for MMIO, its FlatImp execution needs to be
     passed the whole memory, and that's why we also need the whole memory for FlatImp here. *)
  Lemma compile_stmt_correct_aux:
    forall (s: @stmt (@FlatImp.syntax_params (@FlatImp_params p))) t initialMH initialRegsH initialMetrics postH R,
    eval_stmt s t initialMH initialRegsH initialMetrics postH ->
    forall initialL insts,
    @compile_stmt def_params iset s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getMetrics) = initialMetrics ->
    initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
    ext_guarantee initialL ->
    runsTo initialL (fun finalL => exists finalML finalMetrics,
          postH finalL.(getLog) finalML finalL.(getRegs) finalMetrics /\
          (program initialL.(getPc) insts * eq finalML * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
          finalL.(getNextPc) = add finalL.(getPc) (ZToReg 4) /\
          ext_guarantee finalL).
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      lazymatch goal with
      | H1: valid_registers ?s, H2: stmt_not_too_big ?s |- _ =>
        pose proof (compile_stmt_emits_valid _ doesSupportM H1 H2)
      end;
      simpl in *;
      destruct_everything.

    - (* SInteract *)
      eapply runsTo_weaken.
      + eapply compile_ext_call_correct with (postH := post) (action0 := action)
                                             (argvars0 := argvars) (resvars0 := resvars);
          simpl; reflexivity || eassumption || seplog || idtac.
        eapply @ExInteract; try eassumption.
      + simpl. intros finalL A. destruct_RiscvMachine finalL. simpl in *.
        destruct_products. subst. eauto 7.
    - (* SCall *)
      match goal with
      | A: map.get map.empty _ = Some _ |- _ =>
        clear -A; exfalso; simpl in *;
        rewrite (map.get_empty (ok := env_ok)) in A
      end.
      discriminate.

    - (* SLoad *)
      unfold Memory.load in *. simp.
      assert (exists R0, (truncated_scalar sz addr z * R0)%sep m) as A by admit.
      destruct A as [R0 A].
      eapply det_step.
      + eapply go_fetch_inst.
        * reflexivity.
        * seplog.
        * unfold valid_instructions in *.
          match goal with
          | H: forall (_: Instruction), _ |- _ => apply H; constructor; reflexivity
          end.
        * eapply go_load; try eassumption. 2: eapply go_step; simpl; reflexivity.
          simpl.

          unfold Memory.load.
          evar (HLR: mem -> Prop). evar (LLR: mem -> Prop).
          erewrite load_Z_of_sep with (R1 := (HLR * LLR)%sep); [reflexivity|].
          subst HLR LLR.
          eapply sep_assoc.

          eapply seplog_subst_eq.
          { exact H8. }
          { ecancel. }
          { exact A. }
      + run1done. eexists. eexists. repeat split; try eassumption.
        * match goal with
          | H: post _ _ (map.put _ _ ?v) _ |- post _ _ (map.put _ _ ?v') _ =>
            assert (v = v') as F
          end.
          { (* TODO meh why so many conversions? *) admit. }
          rewrite <- F. eassumption.
        * solve_word_eq word_ok.
        * eapply ext_guarantee_preservable; [eassumption | simpl; intuition idtac | reflexivity ].

    - (* SStore *)
      eapply det_step.
      + eapply go_fetch_inst.
        * reflexivity.
        * seplog.
        * unfold valid_instructions in *.
          match goal with
          | H: forall (_: Instruction), _ |- _ => apply H; constructor; reflexivity
          end.
        * eapply go_store; try eassumption.
          { admit. }
          { eapply go_step. simpl. reflexivity. }
      + run1done.
        (*
    - (* SLit *)
      subst. destruct_containsProgram.
      eapply compile_lit_correct_full; [sidecondition..|].
      simpl in *.
      run1done.
      f_equal.
      apply compile_lit_correct.

      (* SOp *)
    - match goal with
      | o: bopname |- _ => destruct o (* do this before destruct_containsProgram *)
      end;
      simpl in *; destruct_everything;
      try solve [run1step; run1done].
      (* all except eq are implemented with one instruction *)
      run1step. run1step. run1done.
      rewrite reduce_eq_to_sub_and_lt.
      state_calc.

    - (* SSet *)
      simpl in *; destruct_everything.
      run1step.
      run1done.
      f_equal.
      ring.

    - (* SIf/Then *)
      (* branch if cond = false (will not branch *)
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + (* use IH for then-branch *)
        spec_IH IHfuelH IH s1.
        apply (runsToSatisfying_trans IH). clear IH.
        (* jump over else-branch *)
        intros.
        destruct_everything.
        run1step.
        run1done.

    - (* SIf/Else *)
      (* branch if cond = 0 (will  branch) *)
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + simpl.
        (* use IH for else-branch *)
        spec_IH IHfuelH IH s2.
        IH_done IH.
    - (* SLoop/done *)
      (* We still have to run part 1 of the loop body which is before the break *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + run1done.

    - (* SLoop/again *)
      (* 1st application of IH: part 1 of loop body *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + (* 2nd application of IH: part 2 of loop body *)
        spec_IH IHfuelH IH s2.
        apply (runsToSatisfying_trans IH). clear IH.
        intros.
        destruct_everything.
        run1step.
        (* 3rd application of IH: run the whole loop again *)
        spec_IH IHfuelH IH (SLoop s1 cond s2).
        IH_done IH.

    - (* SSeq *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      spec_IH IHfuelH IH s2.
      IH_done IH.

    - (* SSkip *)
      run1done.

  Qed.
  *) Admitted.

  (*
  Lemma compile_stmt_correct:
    forall imemStart fuelH s insts initialMH finalH finalMH initialL,
    compile_stmt s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 imemStart ->
    eval_stmt _ _ empty_map fuelH empty_map initialMH s = Some (finalH, finalMH) ->
    containsMem initialL.(machineMem) initialMH ->
    containsProgram initialL.(machineMem) insts imemStart ->
    initialL.(core).(pc) = imemStart ->
    initialL.(core).(nextPC) = add initialL.(core).(pc) (ZToReg 4) ->
    mem_inaccessible initialMH (regToZ_unsigned imemStart) (4 * Zlength insts) ->
    exists fuelL,
      let finalL := execState (run (B := BitWidth) fuelL) initialL in
      extends finalL.(core).(registers) finalH /\
      containsMem finalL.(machineMem) finalMH.
  Proof.
    intros.
    pose proof runsTo_to_onerun as Q.
    specialize (Q initialL
                  (fun finalL => extends (registers (core finalL)) finalH /\
                                 containsMem (machineMem finalL) finalMH)).
    cbv beta zeta in *.
    unfold runsTo_onerun in Q.
    destruct Q as [fuel Q].
    {
    eapply runsToSatisfying_imp.
    - eapply @compile_stmt_correct_aux with (s := s) (initialH := empty_map)
        (fuelH := fuelH) (finalH := finalH) (instsBefore := nil) (instsAfter := nil).
      + reflexivity.
      + reflexivity.
      + assumption.
      + assumption.
      + eassumption.
      + eassumption.
      + clear. unfold extends. intros. rewrite empty_is_empty in H. discriminate.
      + assumption.
      + rewrite app_nil_r. rewrite app_nil_l. subst *. assumption.
      + simpl. subst imemStart.
        rewrite Zlength_nil.
        ring.
      + assumption.
      + rewrite app_nil_r. rewrite app_nil_l. subst *. assumption.
    - intros.
      rename H9 into A.
      cbv beta in A. tauto.
    }
    {
      match type of Q with
      | context [?r] =>
          match r with
          | run fuel initialL => destruct r as [ [ u | ] final ] eqn: E; [|contradiction]
          end
      end.
      exists fuel. unfold execState.
      change Register with Z in *.
      rewrite E.
      exact Q.
    }
  Qed.
  *)

End FlatToRiscv1.
