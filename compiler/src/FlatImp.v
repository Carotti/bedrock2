Require Import lib.LibTacticsMin.
Require Import riscv.util.Monads.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import riscv.MinimalLogging.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.Memory.
Require Import compiler.Decidable.

Section FlatImp1.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Variable var: Set.
  Variable func: Set.

  Context {stateMap: MapFunctions var mword}.
  Notation state := (map var mword).
  Notation vars := (set var).

  Ltac state_calc := state_calc_generic var mword.

  Inductive stmt: Set :=
    | SLoad(x: var)(a: var): stmt
    | SStore(a: var)(v: var): stmt
    | SLit(x: var)(v: Z): stmt
    | SOp(x: var)(op: bopname)(y z: var): stmt
    | SSet(x y: var): stmt
    | SIf(cond: var)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: var)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt
    | SCall(binds: list var)(f: func)(args: list var).

  Section WithEnv.
    Context {funcMap: MapFunctions func (list var * list var * stmt)}.
    Notation env := (map func (list var * list var * stmt)).
    Context (e: env).

    (* If we want a bigstep evaluation relation, we either need to put
       fuel into the SLoop constructor, or give it as argument to eval *)
    Fixpoint eval_stmt(f: nat)(st: state)(m: mem)(s: stmt): option (state * mem) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
            a <- get st a;
            v <- read_mem a m;
            Return (put st x v, m)
        | SStore a v =>
            a <- get st a;
            v <- get st v;
            m <- write_mem a v m;
            Return (st, m)
        | SLit x v =>
            Return (put st x (ZToReg v), m)
        | SOp x op y z =>
            y <- get st y;
            z <- get st z;
            Return (put st x (eval_binop op y z), m)
        | SSet x y =>
            v <- get st y;
            Return (put st x v, m)
        | SIf cond bThen bElse =>
            vcond <- get st cond;
            eval_stmt f st m (if reg_eqb vcond (ZToReg 0) then bElse else bThen)
        | SLoop body1 cond body2 =>
            p <- eval_stmt f st m body1;
            let '(st, m) := p in
            vcond <- get st cond;
            if reg_eqb vcond (ZToReg 0) then Return (st, m) else
              q <- eval_stmt f st m body2;
              let '(st, m) := q in
              eval_stmt f st m (SLoop body1 cond body2)
        | SSeq s1 s2 =>
            p <- eval_stmt f st m s1;
            let '(st, m) := p in
            eval_stmt f st m s2
        | SSkip => Return (st, m)
        | SCall binds fname args =>
          fimpl <- get e fname;
          let '(params, rets, fbody) := fimpl in
          argvs <- option_all (List.map (get st) args);
          st0 <- putmany params argvs empty_map;
          st1m' <- eval_stmt f st0 m fbody;
          let '(st1, m') := st1m' in
          retvs <- option_all (List.map (get st1) rets);
          st' <- putmany binds retvs st;
          Return (st', m')
        end
      end.

    Fixpoint eval_stmt_log(f: nat)(st: state)(log: MetricLog)(m: mem)(s: stmt): option (state * MetricLog * mem) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
            a <- get st a;
            v <- read_mem a m;
            Return (put st x v, incMetricInstructions (incMetricLoads log), m)
        | SStore a v =>
            a <- get st a;
            v <- get st v;
            m <- write_mem a v m;
            Return (st, incMetricInstructions (incMetricStores log), m)
        | SLit x v =>
            Return (put st x (ZToReg v), incMetricInstructions_n 15 log, m)
        | SOp x op y z =>
            y <- get st y;
            z <- get st z;
            Return (put st x (eval_binop op y z), incMetricInstructions_n 3 log, m)
        | SSet x y =>
            v <- get st y;
            Return (put st x v, incMetricInstructions log, m)
        | SIf cond bThen bElse =>
            vcond <- get st cond;
            eval_stmt_log f st (incMetricInstructions_n 2 (incMetricJumps log)) m (if reg_eqb vcond (ZToReg 0) then bElse else bThen)
        | SLoop body1 cond body2 =>
            p <- eval_stmt_log f st log m body1;
            let '(st, log, m) := p in
            vcond <- get st cond;
            if reg_eqb vcond (ZToReg 0) then Return (st, incMetricInstructions (incMetricJumps log), m) else
              q <- eval_stmt_log f st log m body2;
              let '(st, log, m) := q in
              eval_stmt_log f st (incMetricInstructions_n 2 (incMetricJumps log)) m (SLoop body1 cond body2)
        | SSeq s1 s2 =>
            p <- eval_stmt_log f st log m s1;
            let '(st, log, m) := p in
            eval_stmt_log f st log m s2
        | SSkip => Return (st, log, m)
        | SCall binds fname args =>
          fimpl <- get e fname;
          let '(params, rets, fbody) := fimpl in
          argvs <- option_all (List.map (get st) args);
          st0 <- putmany params argvs empty_map;
          st1m' <- eval_stmt_log f st0 (incMetricInstructions (incMetricJumps log)) m fbody;
          let '(st1, log, m') := st1m' in
          retvs <- option_all (List.map (get st1) rets);
          st' <- putmany binds retvs st;
          Return (st', log, m')
        end
      end.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      repeat match goal with
             | E: reg_eqb _ _ = true  |- _ => apply reg_eqb_true  in E
             | E: reg_eqb _ _ = false |- _ => apply reg_eqb_false in E
             end;
      inversionss;
      try (unfold_log_inc_dec; fold_log);
      eauto 17.

    Lemma invert_eval_SLoad: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SLoad x y) = Some final ->
      exists a v, get initialSt y = Some a /\
                  read_mem a initialM = Some v /\
                  final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoad_log: forall fuel initialSt initialM x y final log,
      eval_stmt_log (S fuel) initialSt log initialM (SLoad x y) = Some final ->
      exists a v, get initialSt y = Some a /\
                  read_mem a initialM = Some v /\
                  final = (put initialSt x v, incMetricInstructions (incMetricLoads log), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SStore x y) = Some final ->
      exists a v finalM, get initialSt x = Some a /\
                         get initialSt y = Some v /\
                         write_mem a v initialM = Some finalM /\
                         final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore_log: forall fuel initialSt initialM x y final log,
      eval_stmt_log (S fuel) initialSt log initialM (SStore x y) = Some final ->
      exists a v finalM, get initialSt x = Some a /\
                         get initialSt y = Some v /\
                         write_mem a v initialM = Some finalM /\
                         final = (initialSt, incMetricInstructions (incMetricStores log), finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
      eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
      final = (put initialSt x (ZToReg v), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLit_log: forall fuel initialSt initialM x v final log,
      eval_stmt_log (S fuel) initialSt log initialM (SLit x v) = Some final ->
      final = (put initialSt x (ZToReg v), incMetricInstructions_n 15 log, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SOp: forall fuel x y z op initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SOp x op y z) = Some final ->
      exists v1 v2,
        get initialSt y = Some v1 /\
        get initialSt z = Some v2 /\
        final = (put initialSt x (eval_binop op v1 v2), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SOp_log: forall fuel x y z op initialSt initialM final log,
      eval_stmt_log (S fuel) initialSt log initialM (SOp x op y z) = Some final ->
      exists v1 v2,
        get initialSt y = Some v1 /\
        get initialSt z = Some v2 /\
        final = (put initialSt x (eval_binop op v1 v2), incMetricInstructions_n 3 log, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSet: forall fuel x y initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SSet x y) = Some final ->
      exists v,
        get initialSt y = Some v /\ final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSet_log: forall fuel x y initialSt initialM final log,
      eval_stmt_log (S fuel) initialSt log initialM (SSet x y) = Some final ->
      exists v,
        get initialSt y = Some v /\ final = (put initialSt x v, incMetricInstructions log, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SIf: forall fuel cond bThen bElse initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SIf cond bThen bElse) = Some final ->
      exists vcond,
        get initialSt cond = Some vcond /\
        (vcond <> ZToReg 0 /\ eval_stmt fuel initialSt initialM bThen = Some final \/
         vcond =  ZToReg 0 /\ eval_stmt fuel initialSt initialM bElse = Some final).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SIf_log: forall fuel cond bThen bElse initialSt initialM final log,
      eval_stmt_log (S fuel) initialSt log initialM (SIf cond bThen bElse) = Some final ->
      exists vcond,
        get initialSt cond = Some vcond /\
        (vcond <> ZToReg 0 /\ eval_stmt_log fuel initialSt (incMetricInstructions_n 2 (incMetricJumps log)) initialM bThen = Some final \/
         vcond =  ZToReg 0 /\ eval_stmt_log fuel initialSt (incMetricInstructions_n 2 (incMetricJumps log)) initialM bElse = Some final).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoop: forall fuel st1 m1 body1 cond body2 p4,
      eval_stmt (S fuel) st1 m1 (SLoop body1 cond body2) = Some p4 ->
      eval_stmt fuel st1 m1 body1 = Some p4 /\ get (fst p4) cond = Some (ZToReg 0) \/
      exists st2 m2 st3 m3 cv, eval_stmt fuel st1 m1 body1 = Some (st2, m2) /\
                               get st2 cond = Some cv /\ cv <> ZToReg 0 /\
                               eval_stmt fuel st2 m2 body2 = Some (st3, m3) /\
                               eval_stmt fuel st3 m3 (SLoop body1 cond body2) = Some p4.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoop_log: forall fuel st1 m1 body1 cond body2 log1 stf logf mf,
      eval_stmt_log (S fuel) st1 log1 m1 (SLoop body1 cond body2) = Some (stf, logf, mf) ->
      eval_stmt_log fuel st1 log1 m1 body1 = Some (stf, decMetricInstructions (decMetricJumps logf), mf)
        /\ get stf cond = Some (ZToReg 0) \/
      exists st2 m2 st3 m3 cv log2 log3,
         eval_stmt_log fuel st1 log1 m1 body1 = Some (st2, log2, m2) /\
         get st2 cond = Some cv /\ cv <> ZToReg 0 /\
         eval_stmt_log fuel st2 log2 m2 body2 = Some (st3, log3, m3) /\
         eval_stmt_log fuel st3 (incMetricInstructions_n 2 (incMetricJumps log3)) m3 (SLoop body1 cond body2) = Some (stf, logf, mf).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSeq: forall fuel initialSt initialM s1 s2 final,
      eval_stmt (S fuel) initialSt initialM (SSeq s1 s2) = Some final ->
      exists midSt midM, eval_stmt fuel initialSt initialM s1 = Some (midSt, midM) /\
                         eval_stmt fuel midSt midM s2 = Some final.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSeq_log: forall fuel initialSt initialM s1 s2 final log,
      eval_stmt_log (S fuel) initialSt log initialM (SSeq s1 s2) = Some final ->
      exists midSt midM midLog, eval_stmt_log fuel initialSt log initialM s1 = Some (midSt, midLog, midM) /\
                         eval_stmt_log fuel midSt midLog midM s2 = Some final.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSkip: forall fuel initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM SSkip = Some final ->
      final = (initialSt, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSkip_log: forall fuel initialSt initialM final log,
      eval_stmt_log (S fuel) initialSt log initialM SSkip = Some final ->
      final = (initialSt, log, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SCall : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SCall binds fname args) = Some p2 ->
      exists params rets fbody argvs st0 st1 m' retvs st',
        get e fname = Some (params, rets, fbody) /\
        option_all (List.map (get st) args) = Some argvs /\
        putmany params argvs empty_map = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (get st1) rets) = Some retvs /\
        putmany binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SCall_log : forall st m1 st2 m2 logf f binds fname args log,
      eval_stmt_log (S f) st log m1 (SCall binds fname args) = Some (st2, logf, m2) ->
      exists params rets fbody argvs st0 st1 m' retvs st' log',
        get e fname = Some (params, rets, fbody) /\
        option_all (List.map (get st) args) = Some argvs /\
        putmany params argvs empty_map = Some st0 /\
        eval_stmt_log f st0 (incMetricInstructions (incMetricJumps log)) m1 fbody = Some (st1, log', m') /\
        option_all (List.map (get st1) rets) = Some retvs /\
        putmany binds retvs st = Some st' /\
        (st2, logf, m2) = (st', log', m').
    Proof. inversion_lemma. Qed.

  End WithEnv.

  Definition stmt_size_body(rec: stmt -> nat)(s: stmt): nat :=
    match s with
    | SLoad x a => 1
    | SStore a v => 1
    | SLit x v => 8
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (rec bThen) + (rec bElse)
    | SLoop body1 cond body2 => 1 + (rec body1) + (rec body2)
    | SSeq s1 s2 => 1 + (rec s1) + (rec s2)
    | SSkip => 1
    | SCall binds f args => S (length binds + length args)
    end.

  Context {varset: SetFunctions var}.
  Context {func_eq_dec: DecidableEq func}.

  Fixpoint stmt_size(s: stmt): nat := stmt_size_body stmt_size s.
  (* TODO: in coq 8.9 it will be possible to state this lemma automatically: https://github.com/coq/coq/blob/91e8dfcd7192065f21273d02374dce299241616f/CHANGES#L16 *)
  Lemma stmt_size_unfold : forall s, stmt_size s = stmt_size_body stmt_size s. destruct s; reflexivity. Qed.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): vars :=
    match s with
    | SLoad x y => singleton_set x
    | SStore x y => empty_set
    | SLit x v => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y => singleton_set x
    | SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | SSkip => empty_set
    | SCall binds func args => of_list binds
    end.

  Fixpoint accessedVars(s: stmt): vars :=
    match s with
    | SLoad x y => union (singleton_set x) (singleton_set y)
    | SStore x y => union (singleton_set x) (singleton_set y)
    | SLit x v => singleton_set x
    | SOp x op y z => union (singleton_set x) (union (singleton_set y) (singleton_set z))
    | SSet x y => union (singleton_set x) (singleton_set y)
    | SIf cond bThen bElse =>
        union (singleton_set cond) (union (accessedVars bThen) (accessedVars bElse))
    | SLoop body1 cond body2 =>
        union (singleton_set cond) (union (accessedVars body1) (accessedVars body2))
    | SSeq s1 s2 =>
        union (accessedVars s1) (accessedVars s2)
    | SSkip => empty_set
    | SCall binds func args => union (of_list binds) (of_list args)
    end.

  Lemma modVars_subset_accessedVars: forall s,
    subset (modVars s) (accessedVars s).
  Proof.
    intro s. induction s; simpl; unfold singleton_set; state_calc.
  Qed.
End FlatImp1.


Ltac invert_eval_stmt :=
  lazymatch goal with
  | E: eval_stmt _ _ _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad in E
    | apply invert_eval_SStore in E
    | apply invert_eval_SLit in E
    | apply invert_eval_SOp in E
    | apply invert_eval_SSet in E
    | apply invert_eval_SIf in E
    | apply invert_eval_SLoop in E
    | apply invert_eval_SSeq in E
    | apply invert_eval_SSkip in E
    | apply invert_eval_SCall in E ];
    deep_destruct E;
    [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLit" in pose proof tt as x; move x at top
    | let x := fresh "Case_SOp" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top
    | let x := fresh "Case_SCall" in pose proof tt as x; move x at top ]
  end.

Ltac invert_eval_stmt_log :=
  lazymatch goal with
  | E: eval_stmt_log _ _ _ (S ?fuel) _ _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad_log in E
    | apply invert_eval_SStore_log in E
    | apply invert_eval_SLit_log in E
    | apply invert_eval_SOp_log in E
    | apply invert_eval_SSet_log in E
    | apply invert_eval_SIf_log in E
    | apply invert_eval_SLoop_log in E
    | apply invert_eval_SSeq_log in E
    | apply invert_eval_SSkip_log in E
    | apply invert_eval_SCall_log in E ];
    deep_destruct E;
    [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLit" in pose proof tt as x; move x at top
    | let x := fresh "Case_SOp" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top
    | let x := fresh "Case_SCall" in pose proof tt as x; move x at top ]
  end.

Arguments SLoad   {_} {_}.
Arguments SStore  {_} {_}.
Arguments SLit    {_} {_}.
Arguments SOp     {_} {_}.
Arguments SSet    {_} {_}.
Arguments SIf     {_} {_}.
Arguments SLoop   {_} {_}.
Arguments SSeq    {_} {_}.
Arguments SSkip   {_} {_}.
Arguments SCall   {_} {_}.

Section FlatImp2.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Variable var: Set.
  Context {var_eq_dec: DecidableEq var}.
  Variable func: Set.
  Context {func_eq_dec: DecidableEq func}.

  Context {stateMap: MapFunctions var mword}.
  Notation state := (map var mword).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Context {funcMap: MapFunctions func (list var * list var * stmt var func)}.
  Notation env := (map func (list var * list var * stmt var func)).

  Ltac state_calc := state_calc_generic var mword.

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 (e: env) initialSt initialM s final,
    fuel1 <= fuel2 ->
    eval_stmt var func e fuel1 initialSt initialM s = Some final ->
    eval_stmt var func e fuel2 initialSt initialM s = Some final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|].
      assert (fuel1 <= fuel2) as F by omega. specialize IHfuel1 with (1 := F).
      destruct final as [finalSt finalM].
      invert_eval_stmt; cbn in *;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          ensure_new IH'
      end;
      repeat match goal with
      | H: _ = Some _ |- _ => rewrite H
      end;
      try congruence;
      try simpl_if;
      rewrite? (proj2 (reg_eqb_true _ _) eq_refl);
      repeat match goal with
             | H:     (@eq mword _ _)  |- _ => apply reg_eqb_eq in H; rewrite H
             | H: not (@eq mword _ _)  |- _ => apply reg_eqb_ne in H; rewrite H
             end;
      rewrite? reg_eqb_eq by reflexivity;
      eauto.
  Qed.

  Lemma increase_fuel_still_Success_log: forall fuel1 fuel2 (e: env) initialSt initialM s final initialLog,
    fuel1 <= fuel2 ->
    eval_stmt_log var func e fuel1 initialSt initialLog initialM s = Some final ->
    eval_stmt_log var func e fuel2 initialSt initialLog initialM s = Some final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|].
      assert (fuel1 <= fuel2) as F by omega. specialize IHfuel1 with (1 := F).
      destruct final as [[finalSt finalLog] finalM].
      invert_eval_stmt_log; cbn in *;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          ensure_new IH'
      end;
      repeat match goal with
      | H: _ = Some _ |- _ => rewrite H
      end;
      try congruence;
      try simpl_if;
      rewrite? (proj2 (reg_eqb_true _ _) eq_refl);
      repeat match goal with
             | H:     (@eq mword _ _)  |- _ => apply reg_eqb_eq in H; rewrite H
             | H: not (@eq mword _ _)  |- _ => apply reg_eqb_ne in H; rewrite H
             end;
      rewrite? reg_eqb_eq by reflexivity;
      try (repeat f_equal; unfold_log_inc_dec; fold_log);
      eauto.
  Qed.

  Lemma modVarsSound: forall fuel e s initialSt initialM finalSt finalM,
    eval_stmt var func e fuel initialSt initialM s = Some (finalSt, finalM) ->
    only_differ initialSt (modVars var func s) finalSt.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_stmt; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      state_calc.
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.

  Lemma modVarsSound_log: forall fuel e s initialSt initialM initialLog finalSt finalM finalLog,
    eval_stmt_log var func e fuel initialSt initialLog initialM s = Some (finalSt, finalLog, finalM) ->
    only_differ initialSt (modVars var func s) finalSt.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_stmt_log; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      state_calc.
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.

End FlatImp2.
