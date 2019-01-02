Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import bbv.DepEqNat.
Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Export bedrock2.Syntax.
Require Export bedrock2.Semantics.
Require Import bedrock2.Macros.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.Decidable.
Require Import compiler.Memory.
Require Import riscv.MinimalLogging.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Section ExprImp1.

  Context {p : unique! Semantics.parameters}.

  Notation mword := (@Semantics.word p).
  Context {MW: MachineWidth mword}.  
  
  Notation var := (@varname (@syntax p)).
  Notation func := (@funname (@syntax p)).

  Context {stateMap: MapFunctions var (mword)}.
  Notation state := (map var mword).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Hypothesis actname_empty: actname = Empty_set.
  
  Ltac state_calc := state_calc_generic (@varname (@syntax p)) (@Semantics.word p).
  Ltac set_solver := set_solver_generic (@varname (@syntax p)).

  Fixpoint eval_expr(st: state)(e: expr): option mword :=
    match e with
    | expr.literal v => Some (ZToReg v)
    | expr.var x => get st x
    | expr.load x a => None (* TODO *)
    | expr.op op e1 e2 =>
        'Some v1 <- eval_expr st e1;
        'Some v2 <- eval_expr st e2;
        Some (interp_binop op v1 v2)
    end.

  Fixpoint eval_expr_log(st: state)(l: MetricLog)(e: expr): option (MetricLog * mword) :=
    match e with
    | expr.literal v => Some (incMetricInstructions l, ZToReg v)
    | expr.var x => match get st x with
                    | None => None
                    | Some z => Some (incMetricInstructions l, z)
                    end
    | expr.load x a => None (* TODO *)
    | expr.op op e1 e2 =>
        'Some v1 <- eval_expr_log st l e1;
        'Some v2 <- eval_expr_log st (fst v1) e2;
        Some (incMetricInstructions (fst v2), interp_binop op (snd v1) (snd v2))
    end.

  Section WithEnv.
    Context {funcMap: MapFunctions func (list var * list var * cmd)}.
    Notation env := (map func (list var * list var * cmd)).
    Context (e: env).
   
    Fixpoint eval_cmd(f: nat)(st: state)(m: @mem mword)(s: cmd): option (state * (@mem mword)) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | cmd.store number_of_bytes_IGNORED_TODO a v =>
            'Some a <- eval_expr st a;
            'Some v <- eval_expr st v;
            'Some m <- write_mem a v m;
            Some (st, m)
        | cmd.set x e =>
            'Some v <- eval_expr st e;
            Some (put st x v, m)
        (*| cmd.unset x =>
            Some (remove_key st x, m)*)
        | cmd.cond cond bThen bElse =>
            'Some v <- eval_expr st cond;
            eval_cmd f st m (if reg_eqb v (ZToReg 0) then bElse else bThen)
        | cmd.while cond body =>
            'Some v <- eval_expr st cond;
            if reg_eqb v (ZToReg 0) then Some (st, m) else
              'Some (st, m) <- eval_cmd f st m body;
              eval_cmd f st m (cmd.while cond body)
        | cmd.seq s1 s2 =>
            'Some (st, m) <- eval_cmd f st m s1;
            eval_cmd f st m s2
        | cmd.skip => Some (st, m)
        | cmd.call binds fname args =>
          'Some (params, rets, fbody) <- get e fname;
          'Some argvs <- option_all (List.map (eval_expr st) args);
          'Some st0 <- putmany params argvs empty_map;
          'Some (st1, m') <- eval_cmd f st0 m fbody;
          'Some retvs <- option_all (List.map (get st1) rets);
          'Some st' <- putmany binds retvs st;
          Some (st', m')
        | cmd.interact _ _ _ => None (* unsupported *)
        end
      end.

    Fixpoint evaluate_call_args_log (st: state) (args: list expr) (l : MetricLog) :=
      match args with
      | [] => Some ([], l)
      | a :: t =>
        'Some (l', v) <- eval_expr_log st l a;
        'Some (args, finalL) <- evaluate_call_args_log st t l';
        Some (v :: args, finalL)
      end.

    Fixpoint eval_cmd_log(f: nat)(st: state)(l: MetricLog)(m: @mem mword)(s: cmd): option (state *  MetricLog * (@mem mword)) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | cmd.store number_of_bytes_IGNORED_TODO a v =>
            'Some (l, a) <- eval_expr_log st l a;
            'Some (l, v) <- eval_expr_log st l v;
            'Some m <- write_mem a v m;
            Some (st, incMetricInstructions l, m)
        | cmd.set x e =>
            'Some (l, v) <- eval_expr_log st l e;
            Some (put st x v, incMetricInstructions l, m)
        (*| cmd.unset x =>
            Some (remove_key st x, m)*)
        | cmd.cond cond bThen bElse =>
            'Some (l, v) <- eval_expr_log st l cond;
            eval_cmd_log f st (incMetricInstructions l) m (if reg_eqb v (ZToReg 0) then bElse else bThen)
        | cmd.while cond body =>
            'Some (l, v) <- eval_expr_log st l cond;
            if reg_eqb v (ZToReg 0) then Some (st, incMetricInstructions l, m) else
              'Some (st, l, m) <- eval_cmd_log f st (incMetricInstructions l) m body;
              eval_cmd_log f st l m (cmd.while cond body)
        | cmd.seq s1 s2 =>
            'Some (st, l, m) <- eval_cmd_log f st l m s1;
            eval_cmd_log f st l m s2
        | cmd.skip => Some (st, l, m)
        | cmd.call binds fname args =>
          'Some (params, rets, fbody) <- get e fname;
          'Some (argvs, l) <- evaluate_call_args_log st args l;
          'Some st0 <- putmany params argvs empty_map;
          'Some (st1, l, m') <- eval_cmd_log f st0 l m fbody;
          'Some retvs <- option_all (List.map (get st1) rets);
          'Some st' <- putmany binds retvs st;
          Some (st', incMetricInstructions l, m')
        | cmd.interact _ _ _ => None (* unsupported *)
        end
      end.

    Fixpoint expr_size(e: expr): nat :=
      match e with
      | expr.literal _ => 8
      | expr.load _ e => S (expr_size e)
      | expr.var _ => 1
      | expr.op op e1 e2 => S (S (expr_size e1 + expr_size e2))
      end.

    Fixpoint cmd_size(s: cmd): nat :=
      match s with
      | cmd.store _ a v => S (expr_size a + expr_size v)
      | cmd.set x e => S (expr_size e)
      | cmd.cond cond bThen bElse => S (expr_size cond + cmd_size bThen + cmd_size bElse)
      | cmd.while cond body => S (expr_size cond + cmd_size body)
      | cmd.seq s1 s2 => S (cmd_size s1 + cmd_size s2)
      | cmd.skip => 1
      | cmd.call binds f args =>
          S (length binds + length args + List.fold_right Nat.add O (List.map expr_size args))
      | cmd.interact _ _ _ => 1
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
      eauto 16.

    Lemma invert_eval_store: forall fuel initialSt initialM a v final nbytes,
      eval_cmd (S fuel) initialSt initialM (cmd.store nbytes a v) = Some final ->
      exists av vv finalM, eval_expr initialSt a = Some av /\
                           eval_expr initialSt v = Some vv /\
                           write_mem av vv initialM = Some finalM /\
                           final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_store_log: forall fuel initialSt initialM a v final nbytes initialLog,
        eval_cmd_log (S fuel) initialSt initialLog initialM (cmd.store nbytes a v) =  Some final ->
        exists av l l' vv finalM, eval_expr_log initialSt initialLog a = Some (l, av) /\
                             eval_expr_log initialSt l v = Some (l', vv) /\
                             write_mem av vv initialM = Some finalM /\
                             final = (initialSt, incMetricInstructions l', finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_set: forall f st1 m1 p2 x e,
        eval_cmd (S f) st1 m1 (cmd.set x e) = Some p2 ->
        exists v, eval_expr st1 e = Some v /\ p2 = (put st1 x v, m1).
    Proof. inversion_lemma. Qed.
      
    Lemma invert_eval_set_log: forall f st1 m1 p2 x e initialLog,
      eval_cmd_log (S f) st1 initialLog m1 (cmd.set x e) = Some p2 ->
      exists l v, eval_expr_log st1 initialLog e = Some (l, v) /\
                  p2 = (put st1 x v, incMetricInstructions l, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_cond: forall f st1 m1 p2 cond bThen bElse,
      eval_cmd (S f) st1 m1 (cmd.cond cond bThen bElse) = Some p2 ->
      exists cv,
        eval_expr st1 cond = Some cv /\ 
        (cv <> ZToReg 0 /\ eval_cmd f st1 m1 bThen = Some p2 \/
         cv = ZToReg 0  /\ eval_cmd f st1 m1 bElse = Some p2).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_cond_log: forall f st1 m1 p2 cond bThen bElse initialLog,
        eval_cmd_log (S f) st1 initialLog m1 (cmd.cond cond bThen bElse) = Some p2 ->
        exists cv l,
          eval_expr_log st1 initialLog cond = Some (l, cv) /\
          (cv <> ZToReg 0 /\
           eval_cmd_log f st1 (incMetricInstructions l) m1 bThen = Some p2 \/
           cv = ZToReg 0  /\
           eval_cmd_log f st1 (incMetricInstructions l) m1 bElse = Some p2).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_while: forall st1 m1 p3 f cond body,
      eval_cmd (S f) st1 m1 (cmd.while cond body) = Some p3 ->
      exists cv,
        eval_expr st1 cond = Some cv /\
        (cv <> ZToReg 0 /\ (exists st2 m2, eval_cmd f st1 m1 body = Some (st2, m2) /\ 
                                     eval_cmd f st2 m2 (cmd.while cond body) = Some p3) \/
         cv = ZToReg 0 /\ p3 = (st1, m1)).
    Proof. inversion_lemma. Qed.
    
    Lemma invert_eval_while_log: forall st1 m1 p3 f cond body initialLog,
        eval_cmd_log (S f) st1 initialLog m1 (cmd.while cond body) = Some p3 ->
        exists cv l,
          eval_expr_log st1 initialLog cond = Some (l, cv) /\
          (cv <> ZToReg 0 /\ (exists st2 l2 m2, eval_cmd_log f st1 (incMetricInstructions l) m1 body = Some (st2, l2, m2) /\ 
                                             eval_cmd_log f st2 l2 m2 (cmd.while cond body) = Some p3) \/
                             cv = ZToReg 0 /\ p3 = (st1, incMetricInstructions l, m1)).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_seq: forall st1 m1 p3 f s1 s2,
      eval_cmd (S f) st1 m1 (cmd.seq s1 s2) = Some p3 ->
      exists st2 m2, eval_cmd f st1 m1 s1 = Some (st2, m2) /\ eval_cmd f st2 m2 s2 = Some p3.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_seq_log: forall st1 m1 p3 f s1 s2 initialLog,
        eval_cmd_log (S f) st1 initialLog m1 (cmd.seq s1 s2) = Some p3 ->
        exists st2 l2 m2, eval_cmd_log f st1 initialLog m1 s1 = Some (st2, l2, m2) /\
                          eval_cmd_log f st2 l2 m2 s2 = Some p3.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_skip: forall st1 m1 p2 f,
      eval_cmd (S f) st1 m1 cmd.skip = Some p2 ->
      p2 = (st1, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_skip_log: forall st1 l1 m1 p2 f,
        eval_cmd_log (S f) st1 l1 m1 cmd.skip = Some p2 ->
        p2 = (st1, l1, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_call : forall st m1 p2 f binds fname args,
      eval_cmd (S f) st m1 (cmd.call binds fname args) = Some p2 ->
      exists params rets fbody argvs st0 st1 m' retvs st',
        get e fname = Some (params, rets, fbody) /\
        option_all (List.map (eval_expr st) args) = Some argvs /\
        putmany params argvs empty_map = Some st0 /\
        eval_cmd f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (get st1) rets) = Some retvs /\
        putmany binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_call_log : forall st l m1 p2 f binds fname args,
        eval_cmd_log (S f) st l m1 (cmd.call binds fname args) = Some p2 ->
        exists params rets fbody argvs st0 st1 l0 l1 m' retvs st',
          get e fname = Some (params, rets, fbody) /\
          evaluate_call_args_log st args l = Some (argvs, l0) /\
          putmany params argvs empty_map = Some st0 /\
          eval_cmd_log f st0 l0 m1 fbody = Some (st1, l1, m') /\
          option_all (List.map (get st1) rets) = Some retvs /\
          putmany binds retvs st = Some st' /\
          p2 = (st', incMetricInstructions l1, m').
    Proof. inversion_lemma. eauto 18. Qed.
      
    Lemma invert_eval_interact : forall st m1 p2 f binds fname args,
      eval_cmd (S f) st m1 (cmd.interact binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_interact_log : forall st l m1 p2 f binds fname args,
      eval_cmd_log (S f) st l m1 (cmd.interact binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

  End WithEnv.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr(e: expr): list var :=
    match e with
    | expr.literal v => []
    | expr.var x => [x]
    | expr.load nbytes e => allVars_expr e
    | expr.op op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_cmd(s: cmd): list var := 
    match s with
    | cmd.store _ a e => (allVars_expr a) ++ (allVars_expr e)
    | cmd.set v e => v :: allVars_expr e
    | cmd.cond c s1 s2 => (allVars_expr c) ++ (allVars_cmd s1) ++ (allVars_cmd s2)
    | cmd.while c body => (allVars_expr c) ++ (allVars_cmd body)
    | cmd.seq s1 s2 => (allVars_cmd s1) ++ (allVars_cmd s2)
    | cmd.skip => []
    | cmd.call binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    | cmd.interact _ _ _ => [] (* TODO *)
    end.

  (* Returns a static approximation of the set of modified vars.
     The returned set might be too big, but is guaranteed to include all modified vars. *)
  Fixpoint modVars(s: cmd): vars := 
    match s with
    | cmd.store _ _ _ => empty_set
    | cmd.set v _ => singleton_set v
    | cmd.cond _ s1 s2 => union (modVars s1) (modVars s2)
    | cmd.while _ body => modVars body
    | cmd.seq s1 s2 => union (modVars s1) (modVars s2)
    | cmd.skip => empty_set
    | cmd.call binds _ _ => of_list binds
    | cmd.interact binds _ _ => of_list binds
    end.

  Lemma modVars_subset_allVars: forall x s,
    x \in modVars s ->
    In x (allVars_cmd s).
  Proof.
    intros.
    induction s; simpl in *.
    - set_solver.
    - set_solver.
    - exfalso. eapply empty_set_spec. eassumption.
    - apply union_spec in H.
      apply in_or_app. right. apply in_or_app.
      destruct H as [H|H]; auto.
    - apply union_spec in H.
      apply in_or_app.
      destruct H as [H|H]; auto.
    - apply in_or_app. right. auto.
    - generalize dependent binds; induction binds; intros H; cbn in *.
      + apply empty_set_spec in H; destruct H.
      + apply union_spec in H; destruct H.
        * left. apply singleton_set_spec in H. auto.
        * right. auto.
    - replace actname with Empty_set in *. destruct action.
  Qed.

End ExprImp1.


Ltac invert_eval_cmd :=
  lazymatch goal with
  | E: eval_cmd _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_skip in E
    | apply invert_eval_set in E
    | apply invert_eval_store in E
    | apply invert_eval_cond in E
    | apply invert_eval_seq in E
    | apply invert_eval_while in E
    | apply invert_eval_call in E
    | apply invert_eval_interact in E ];
    deep_destruct E;
    [ let x := fresh "Case_skip" in pose proof tt as x; move x at top 
    | let x := fresh "Case_set" in pose proof tt as x; move x at top
    | let x := fresh "Case_store" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_seq" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_call" in pose proof tt as x; move x at top
    | let x := fresh "Case_interact" in pose proof tt as x; move x at top
    ]
  end.

Ltac invert_eval_cmd_log :=
  lazymatch goal with
  | E: eval_cmd_log _ (S ?fuel) _ _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_skip_log in E
    | apply invert_eval_set_log in E
    | apply invert_eval_store_log in E
    | apply invert_eval_cond_log in E
    | apply invert_eval_seq_log in E
    | apply invert_eval_while_log in E
    | apply invert_eval_call_log in E
    | apply invert_eval_interact_log in E ];
    deep_destruct E;
    [ let x := fresh "Case_skip" in pose proof tt as x; move x at top 
    | let x := fresh "Case_set" in pose proof tt as x; move x at top
    | let x := fresh "Case_store" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_seq" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_call" in pose proof tt as x; move x at top
    | let x := fresh "Case_interact" in pose proof tt as x; move x at top
    ]
  end.

Section ExprImp2.

  Context {p : unique! Semantics.parameters}.

  Notation mword := (@Semantics.word p).
  Context {MW: MachineWidth mword}.  
  
  Notation var := (@varname (@syntax p)).
  Notation func := (@funname (@syntax p)).

  Context {stateMap: MapFunctions var (mword)}.
  Notation state := (map var mword).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  (* TODO this one should be wrapped somewhere *)
  Context {varname_eq_dec: DecidableEq var}.
  
  Hypothesis actname_empty: actname = Empty_set.
  
  Ltac state_calc := state_calc_generic (@varname (@syntax p)) (@Semantics.word p).
  Ltac set_solver := set_solver_generic (@varname (@syntax p)).

  Context {funcMap: MapFunctions func (list var * list var * @cmd (@syntax p))}.
  Notation env := (map func (list var * list var * cmd)).

  Lemma modVarsSound: forall (e: env) fuel s initialS initialM finalS finalM,
    eval_cmd e fuel initialS initialM s = Some (finalS, finalM) ->
    only_differ initialS (modVars s) finalS.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_cmd; simpl in *; inversionss;
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

End ExprImp2.
