Require Import lib.LibTacticsMin.
Require Import coqutil.Word.Properties.
Require Import compiler.util.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.NameGen.
Require Import coqutil.Decidable.
Require Import riscv.Memory.
Require Import riscv.Utility.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics. (* TODO: this should be in bedrock2.Semantics *)
Require Import coqutil.Macros.unique.
Require Import Coq.Bool.Bool.
Require Import coqutil.Datatypes.PropSet.


Open Scope Z_scope.


Section FlattenExpr.

  Context {p : unique! FlatImp.FlatImp.parameters}.

  Definition todo {t: Type} : t. Admitted.

  Instance semantics_params : Semantics.parameters := {|
    Semantics.syntax := FlatImp.FlatImp.syntax_params;
    Semantics.word := Utility.word;
    Semantics.byte := Utility.byte;
    Semantics.env := todo;
    Semantics.funname_eqb := todo;
    Semantics.ext_spec:= todo;
  |}.

  (* TODO where to put these? *)
  Context {NGstate: Type}.
  Context {NG: NameGen varname NGstate}.
  Context {locals_ok: map.ok locals}.

  Hypothesis actname_empty: Syntax.actname = Empty_set.

  (* TODO partially specify this in Semantics parameters *)
  (*Hypothesis convert_bopname: @Syntax.bopname (@Semantics.syntax p) -> Basic_bopnames.bopname. *)
  (*Hypothesis eval_binop_compat: forall op w w0,
      Op.eval_binop (convert_bopname op) w w0 = Semantics.interp_binop op w w0. *)

  Ltac state_calc0 :=
    map_solver locals_ok.

  Ltac set_solver :=
    set_solver_generic (@varname (@FlatImp.FlatImp.syntax_params p)).

  (* returns stmt and var into which result is saved, and new fresh name generator state
     TODO use state monad? *)
  Fixpoint flattenExpr(ngs: NGstate)(e: Syntax.expr):
    (FlatImp.stmt * varname * NGstate) :=
    match e with
    | Syntax.expr.literal n =>
        let '(x, ngs') := genFresh ngs in
        (FlatImp.SLit x n, x, ngs')
    | Syntax.expr.var x =>
        (* (FlatImp.SSkip, x, ngs)  would be simpler but doesn't satisfy the invariant that
           the returned var is in modVars of the returned statement *)
        let '(y, ngs') := genFresh ngs in
        (FlatImp.SSet y x, y, ngs')
    | Syntax.expr.load sz e =>
        let '(s1, r1, ngs') := flattenExpr ngs e in
        let '(x, ngs'') := genFresh ngs' in
        (FlatImp.SSeq s1 (FlatImp.SLoad sz x r1), x, ngs'')
    | Syntax.expr.op op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' e2 in
        let '(x, ngs''') := genFresh ngs'' in
        (FlatImp.SSeq s1 (FlatImp.SSeq s2 (FlatImp.SOp x op r1 r2)), x, ngs''')
    end.

  Fixpoint flattenExprAsBoolExpr(ngs: NGstate)(e: Syntax.expr):
    (FlatImp.stmt * FlatImp.bcond * NGstate) :=
    match e with
    | Syntax.expr.literal n =>
        let '(stmt, x, ngs') := flattenExpr ngs e in
        (stmt, FlatImp.CondNez x, ngs')
    | Syntax.expr.var x =>
        let '(stmt, x, ngs') := flattenExpr ngs e in
        (stmt, FlatImp.CondNez x, ngs')
    | Syntax.expr.load _ e' =>
        let '(stmt, x, ngs') := flattenExpr ngs e in
        (stmt, FlatImp.CondNez x, ngs')
    | Syntax.expr.op op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' e2 in
        match op with
        | Syntax.bopname.add
        | Syntax.bopname.sub
        | Syntax.bopname.mul
        | Syntax.bopname.and
        | Syntax.bopname.or
        | Syntax.bopname.xor
        | Syntax.bopname.sru
        | Syntax.bopname.slu
        | Syntax.bopname.srs =>
            let '(x, ngs''') := genFresh ngs'' in
            (FlatImp.SSeq s1 (FlatImp.SSeq s2 (FlatImp.SOp x op r1 r2)), FlatImp.CondNez x, ngs''')
        | Syntax.bopname.lts =>
            (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BLt r1 r2, ngs'')
        | Syntax.bopname.ltu =>
            (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BLtu r1 r2, ngs'')
        | Syntax.bopname.eq =>
            (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BEq r1 r2, ngs'')
        end
    end.

  Definition flattenCall(ngs: NGstate)(binds: list varname)(f: Syntax.funname)
             (args: list Syntax.expr):
    FlatImp.stmt * NGstate :=
    let '(compute_args, argvars, ngs) :=
          List.fold_right
            (fun e '(c, vs, ngs) =>
               let (ce_ve, ngs) := flattenExpr ngs e in
               let c := FlatImp.SSeq (fst ce_ve) c in
               (c, snd ce_ve::vs, ngs)
            ) (FlatImp.SSkip, nil, ngs) args in
      (FlatImp.SSeq compute_args (FlatImp.SCall (binds: list varname) f argvars), ngs).

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: Syntax.cmd): (FlatImp.stmt * NGstate) :=
    match s with
    | Syntax.cmd.store sz a v =>
        let '(sa, ra, ngs') := flattenExpr ngs a in
        let '(sv, rv, ngs'') := flattenExpr ngs' v in
        (FlatImp.SSeq sa (FlatImp.SSeq sv (FlatImp.SStore sz ra rv)), ngs'')
    | Syntax.cmd.set x e =>
        let '(e', r, ngs') := flattenExpr ngs e in
        (FlatImp.SSeq e' (FlatImp.SSet x r), ngs')
    | Syntax.cmd.cond cond sThen sElse =>
        let '(cond', bcond, ngs') := flattenExprAsBoolExpr ngs cond in
        let '(sThen', ngs'') := flattenStmt ngs' sThen in
        let '(sElse', ngs''') := flattenStmt ngs'' sElse in
        (FlatImp.SSeq cond' (FlatImp.SIf bcond sThen' sElse'), ngs''')
    | Syntax.cmd.while cond body =>
        let '(cond', bcond, ngs') := flattenExprAsBoolExpr ngs cond in
        let '(body', ngs'') := flattenStmt ngs' body in
        (FlatImp.SLoop cond' bcond body', ngs'')
    | Syntax.cmd.seq s1 s2 =>
        let '(s1', ngs') := flattenStmt ngs s1 in
        let '(s2', ngs'') := flattenStmt ngs' s2 in
        (FlatImp.SSeq s1' s2', ngs'')
    | Syntax.cmd.skip | Syntax.cmd.unset _ => (FlatImp.SSkip, ngs)
    | Syntax.cmd.call binds f args => flattenCall ngs binds f args
    | Syntax.cmd.interact _ _ _ => (FlatImp.SSkip, ngs) (* unsupported *)
    end.

  Arguments Z.add : simpl never.
  Arguments Z.mul : simpl never.

  Lemma flattenExpr_size: forall e s resVar ngs ngs',
    flattenExpr ngs e = (s, resVar, ngs') ->
    0 <= FlatImp.stmt_size s <= 2 * ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp; inversionss;
      simpl; try omega.
    - specializes IHe; [eassumption|]. omega.
    - specializes IHe1; [eassumption|].
      specializes IHe2; [eassumption|].
      omega.
  Qed.

  Lemma flattenExprAsBoolExpr_size: forall e s bcond ngs ngs',
      flattenExprAsBoolExpr ngs e = (s, bcond, ngs') ->
      FlatImp.stmt_size s <= 2 * ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
      inversionss; simpl;
      repeat match goal with
      | H : _ |- _ => apply flattenExpr_size in H
      end; try omega.
  Qed.

  Lemma fold_right_cons: forall (A B: Type) (f: B -> A -> A) (a0: A) (b: B) (bs: list B),
      fold_right f a0 (b :: bs) = f b (fold_right f a0 bs).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma flattenCall_size: forall f args binds ngs ngs' s,
      flattenCall ngs binds f args = (s, ngs') ->
      0 < FlatImp.stmt_size s <= 3 * ExprImp.cmd_size (Syntax.cmd.call binds f args).
  Proof.
    intro f.
    induction args; intros.
    - unfold flattenCall in *. simpl in H. inversions H. simpl.
      rewrite! Zcomplements.Zlength_nil in *.
      pose proof (ListLib.Zlength_nonneg binds).
      omega.
    - unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds ngs).
      rewrite E0 in IHargs.
      specialize IHargs with (1 := eq_refl).

      unfold ExprImp.cmd_size.
      unfold ExprImp.cmd_size in IHargs.
      rewrite map_cons. rewrite fold_right_cons.
      destruct p0.
      apply flattenExpr_size in E1.
      simpl in *.
      rewrite! ListLib.Zlength_cons.

      (* PARAMRECORDS ? *)

      (* doesn't match
      forget (@map expr Z (@ExprImp.expr_size semantics_params) args) as FR. *)

      lazymatch goal with
      | H: context [fold_right Z.add 0 ?a] |- context [fold_right Z.add 0 ?a'] =>
        constr_eq a a';
        forget (fold_right Z.add 0 a) as FR
      end.

      repeat match goal with
      | H: context [Zcomplements.Zlength ?a] |- _ =>
        let n := fresh "l" in
        forget (Zcomplements.Zlength a) as n
      | e: expr |- _ => unique pose proof (ExprImp.expr_size_pos e)
      | e: FlatImp.stmt |- _ => unique pose proof (FlatImp.stmt_size_pos e)
      end.

      forget (FlatImp.stmt_size s) as sz0.
      forget (FlatImp.stmt_size s1) as sz1.
      forget (ExprImp.expr_size a) as esz.

      match goal with
      | |- 0 < ?a <= ?b => ring_simplify a b
      end.
      lazymatch type of IHargs with
      | 0 < ?a <= ?b => ring_simplify a b in IHargs
      end.

      Lia.lia.
  Qed.

  Lemma flattenStmt_size: forall s s' ngs ngs',
    flattenStmt ngs s = (s', ngs') ->
    0 < FlatImp.stmt_size s' <= 3 * ExprImp.cmd_size s.
  Proof.
    induction s; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl;
    repeat match goal with
    | IH: _, A: _ |- _ => specialize IH with (1 := A)
    end;
    repeat match goal with
    | H: flattenExpr _ _ = _ |- _ => apply flattenExpr_size in H
    | H: flattenExprAsBoolExpr _ _ = _ |- _ => apply flattenExprAsBoolExpr_size in H
    end;
    try omega;
    try eapply flattenCall_size; try eassumption.
  Admitted.

  Lemma flattenExpr_freshVarUsage: forall e ngs ngs' s v,
    flattenExpr ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Lemma flattenExprAsBoolExpr_freshVarUsage: forall e ngs ngs' s v,
    flattenExprAsBoolExpr ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; simpl in *; repeat (destruct_one_match_hyp);
      repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H : genFresh _ = _      |- _ => apply genFresh_spec in H
             | H : flattenExpr _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Lemma flattenExpr_modifies_resVar: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    resVar \in (FlatImp.modVars s).
  Proof.
    intros.
    destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *; set_solver.
  Qed.

  Lemma flattenExprAsBoolExpr_modifies_cond_vars: forall e s ngs ngs' cond,
    flattenExprAsBoolExpr ngs e = (s, cond, ngs') ->
    subset (FlatImp.accessedVarsBcond cond) (FlatImp.modVars s).
  Proof.
    intros.
    destruct e; simpl in *; repeat (destruct_one_match_hyp);
      repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H : flattenExpr _ _ = _ |- _ => apply flattenExpr_modifies_resVar in H
             | |- _ => progress simpl in *
             end; set_solver.
  Qed.

  Lemma flattenExpr_resVar: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    ~ resVar \in (allFreshVars ngs').
  Proof.
    intros. destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *;
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    set_solver.
  Qed.

  Lemma flattenExpr_modVars_spec: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
    simpl;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H: genFresh _ = _      |- _ => apply genFresh_spec in H
             | H: flattenExpr _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
             | |- _ => progress simpl in *
    end;
    try solve [set_solver].
  Qed.

  Lemma flattenExprAsBoolExpr_modVars_spec: forall e s ngs ngs' cond,
    flattenExprAsBoolExpr ngs e = (s, cond, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
    simpl;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
    | H: genFresh _ = _ |- _ => apply genFresh_spec in H
    | H: flattenExpr _ _ = _ |- _ =>
      unique eapply flattenExpr_freshVarUsage in copy of H;
      unique eapply flattenExpr_modVars_spec in copy of H
    | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
    | |- _ => progress simpl in *
    end;
    try solve [set_solver].
  Qed.

  Lemma flattenCall_freshVarUsage: forall f args binds ngs1 ngs2 s,
      flattenCall ngs1 binds f args = (s, ngs2) ->
      subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction args; cbn; intros.
    { inversionss; subst; set_solver. }
    { unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds ngs1).
      rewrite E0 in IHargs.
      specialize IHargs with (1 := eq_refl).
      destruct p0.
      apply flattenExpr_freshVarUsage in E1.
      clear -IHargs E1.
      set_solver. }
  Qed.

  Lemma flattenStmt_freshVarUsage: forall s s' ngs1 ngs2,
    flattenStmt ngs1 s = (s', ngs2) ->
    subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction s; intros; simpl in *; repeat (destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    | H: _ |- _ => apply flattenExpr_freshVarUsage in H
    | H: _ |- _ => apply flattenExprAsBoolExpr_freshVarUsage in H
    | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
    end;
    repeat match goal with
    | IH: forall _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    try solve [set_solver].
    eapply flattenCall_freshVarUsage. eassumption.
  Qed.

  Ltac pose_flatten_var_ineqs :=
    repeat match goal with
    | H: _ |- _ => unique eapply flattenExpr_freshVarUsage in copy of H
    | H: _ |- _ => unique eapply flattenExprAsBoolExpr_freshVarUsage in copy of H
    | H: _ |- _ => unique eapply FlatImp.modVarsSound in copy of H
    | H: _ |- _ => unique eapply flattenExpr_modifies_resVar in copy of H
    | H: _ |- _ => unique eapply flattenExprAsBoolExpr_modifies_cond_vars in copy of H
    | H: _ |- _ => unique eapply flattenExpr_modVars_spec in copy of H
    | H: _ |- _ => unique eapply flattenExprAsBoolExpr_modVars_spec in copy of H
    | H: _ |- _ => unique eapply flattenStmt_freshVarUsage in copy of H
    end.

  Tactic Notation "nofail" tactic3(t) := first [ t | fail 1000 "should not have failed"].

  Ltac fuel_increasing_rewrite :=
    lazymatch goal with
    | Ev:        FlatImp.eval_stmt _ _ ?ENV ?Fuel1 ?initialSt ?initialM ?s = ?final
      |- context [FlatImp.eval_stmt _ _ ?ENV ?Fuel2 ?initialSt ?initialM ?s]
      => let IE := fresh in assert (Fuel1 <= Fuel2) as IE by omega;
         eapply FlatImp.increase_fuel_still_Success in Ev; [|apply IE];
         clear IE;
         rewrite Ev
    end.

  (* only needed if we want to export the goal into a map_solver-only environment *)
  Ltac prepare_for_map_solver :=
    repeat match goal with
             | H: context [allFreshVars ?ngs] |- _ =>
               let n := fresh "fv" ngs in
               forget (allFreshVars ngs) as n
             | H: context [FlatImp.modVars ?var ?func ?s] |- _ =>
               let n := fresh "mv" s in
               forget (FlatImp.modVars var func s) as n
             | H: context [ExprImp.modVars ?s] |- _ =>
               let n := fresh "emv" in
               forget (ExprImp.modVars s) as n
             | H: @eq ?T _ _ |- _ =>
               match T with
            (* | option Semantics.word => don't clear because we have maps of Semantics.word *)
               | nat => clear H
               end
           end;
    repeat match goal with
           | H: context[?x] |- _ =>
             let t := type of x in
             unify t NGstate;
             clear H
           end;
    repeat match goal with
           | x: NGstate |- _ => clear x
           end;
    clear NG NGstate;
    (repeat (so fun hyporgoal => match hyporgoal with
    | context [ZToReg ?x] => let x' := fresh x in forget (ZToReg x) as x'
    end));
    repeat match goal with
           | H: ?P |- _ =>
             progress
               tryif (let T := type of P in unify T Prop)
               then revert H
               else (match P with
                     | DecidableEq _ => idtac
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

  Ltac state_calc := state_calc0.

  (* Note: If you want to get in the conclusion
     "only_differ initialL (vars_range firstFree (S resVar)) finalL"
     this needn't be part of this lemma, because it follows from
     flattenExpr_modVars_spec and FlatImp.modVarsSound *)
  Lemma flattenExpr_correct_aux env : forall e ngs1 ngs2 resVar (s: FlatImp.stmt) (initialH initialL: locals) initialM res,
    flattenExpr ngs1 e = (s, resVar, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    (* TODO why do I have to give semantics_params explicitly? *)
    @eval_expr semantics_params initialM initialH e = Some res ->
    exists (fuel: nat) (finalL: locals),
      FlatImp.eval_stmt env fuel initialL initialM s = Some (finalL, initialM) /\
      map.get finalL resVar = Some res.
  Proof.
    induction e; introv F Ex U Ev.
    - repeat (inversionss; try destruct_one_match_hyp).
      match goal with
      | |- context [map.get _ resVar = Some ?res] =>
         exists 1%nat (map.put initialL resVar res)
      end.
      split; [reflexivity|state_calc].
    - repeat (inversionss; try destruct_one_match_hyp).
      exists 1%nat (map.put initialL resVar res). repeat split.
      + simpl. unfold map.extends in Ex. apply Ex in H0.

        (* PARAMRECORDS *)
        Fail rewrite H0.
        Set Printing Implicit.
        simpl in *.
        rewrite H0.
        Unset Printing Implicit.

        reflexivity.

      + state_calc.
    - admit. (* load *)
    - repeat (inversionss; try destruct_one_match_hyp).
      pose_flatten_var_ineqs.
      specialize IHe1 with (initialM := initialM) (1 := E) (2 := Ex).
      specializes IHe1. {
        clear IHe2.
        state_calc.
      }
      { eassumption. }
      destruct IHe1 as [fuel1 [midL [Ev1 G1]]].
      progress pose_flatten_var_ineqs.
      specialize IHe2 with (initialH := initialH) (initialL := midL) (initialM := initialM)
         (1 := E0).
      specializes IHe2.
  Admitted.
  (*
      { state_calc. }
      { state_calc. }
      { eassumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 G2]]].
      remember (Datatypes.S (Datatypes.S (fuel1 + fuel2))) as f0.
      remember (Datatypes.S (fuel1 + fuel2)) as f.
      (*                                or     (Op.eval_binop (convert_bopname op) w w0) ? *)
      exists (Datatypes.S f0) (put preFinalL resVar (Semantics.interp_binop op w w0)).
      pose_flatten_var_ineqs.
      split; [|apply get_put_same].
      simpl. fuel_increasing_rewrite.
      subst f0. simpl. fuel_increasing_rewrite.
      subst f. simpl.
      assert (get preFinalL v = Some w) as G1'. {
        state_calc.
      }
      rewrite G1'. simpl. rewrite G2. simpl. repeat f_equal.
      apply eval_binop_compat.
  Qed.
   *)

  Ltac simpl_reg_eqb :=
    rewrite? word.eqb_eq by congruence;
    rewrite? word.eqb_ne by congruence;
    repeat match goal with
           | E: _ _ _ = true  |- _ => apply word.eqb_true  in E
           | E: _ _ _ = false |- _ => apply word.eqb_false in E
           end.

  Ltac cleanup_options :=
    repeat match goal with
    | H : Some _ = Some _ |- _ =>
        invert_Some_eq_Some
    | |- Some _ = Some _ =>
        f_equal
    end; try discriminate.

  Lemma unsigned_ne: forall (a b: word), word.unsigned a <> word.unsigned b -> a <> b.
  Proof.
    intros.
    intro C.
    subst b.
    apply H.
    reflexivity.
  Qed.

  Lemma one_ne_zero: word.of_Z 1 <> word.of_Z 0.
  Proof.
    apply unsigned_ne.
    rewrite! word.unsigned_of_Z.
    rewrite! Z.mod_small;
      [omega|
       pose proof word.width_pos as P; pose proof (Z.pow_gt_1 2 Utility.width) as Q ..].
    {
      (* PARAMRECORDS *)
      Fail omega.
      unfold width, semantics_params.
      omega.
    }
    {
      (* PARAMRECORDS *)
      Fail omega.
      unfold width, semantics_params.
      omega.
    }
  Qed.

  Lemma flattenBooleanExpr_correct_aux env :
    forall e ngs1 ngs2 resCond (s: FlatImp.stmt)
           (initialH initialL: locals) initialM res,
    flattenExprAsBoolExpr ngs1 e = (s, resCond, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    @eval_expr semantics_params initialM initialH e = Some res ->
    exists (fuel: nat) (finalL: locals),
      FlatImp.eval_stmt env fuel initialL initialM s = Some (finalL, initialM) /\
      FlatImp.eval_bcond finalL resCond = Some (negb (reg_eqb res (ZToReg 0))).
  Proof.
    destruct e; introv F Ex U Ev;
    unfold flattenExprAsBoolExpr in F.
    1,2,3:
      repeat destruct_one_match_hyp; repeat destruct_pair_eqs; subst;
      pose proof flattenExpr_correct_aux as P;
      specialize P with (initialM := initialM) (1 := E) (4 := Ev);
      edestruct P as [fuelS0 [initial2L [Evcond G]]]; [eassumption..| ];
      exists fuelS0 initial2L;
      split; [eassumption| unfold FlatImp.eval_bcond].

    Set Printing Implicit.
    (* PARAMRECORDS *)
    { Fail rewrite G. simpl in G. rewrite G. solve [eauto]. }
    { Fail rewrite G. simpl in G. rewrite G. solve [eauto]. }
    { Fail rewrite G. simpl in G. rewrite G. solve [eauto]. }
    Unset Printing Implicit.

    do 5 destruct_one_match_of_hyp F; repeat destruct_pair_eqs; subst.
    { inversion Ev. repeat destruct_one_match_of_hyp H0.
    - pose proof flattenExpr_correct_aux as P.
      specialize P with (env := env) (initialM := initialM) (1 := E) (4 := E1).
      edestruct P as [fuelS0 [initial2L [Evcond G]]]; [eassumption..| ]; clear P.

      pose proof flattenExpr_correct_aux as Q.
      specialize Q with (initialL := initial2L) (env := env)
                        (initialM := initialM) (1 := E0) (4 := E2).
      pose_flatten_var_ineqs.

      (* PARAMRECORDS ? *)
      Fail edestruct Q as [fuelS1 [initial3L [Evcond2 G2]]]; [solve [state_calc]..|]; clear Q.
      simpl in *.
      edestruct Q as [fuelS1 [initial3L [Evcond2 G2]]]; [solve [state_calc]..|]; clear Q.

      remember (Datatypes.S (Datatypes.S (fuelS0 + fuelS1))) as f0.
      remember (Datatypes.S (fuelS0 + fuelS1)) as f.
      pose_flatten_var_ineqs.
      (*
      assert (map.get initial3L v = Some w) by (state_calc).
      assert ((ZToReg 1) <> (ZToReg 0)) by (apply one_ne_zero).
      *)


      (*
        Error: Anomaly "Universe Top.71868 undefined." Please report at http://coq.inria.fr/bugs/.

      repeat destruct_one_match_of_hyp F; repeat destruct_pair_eqs;
      eexists (Datatypes.S f0); eexists; split; simpl;
      repeat (match goal with
      | H: FlatImp.eval_stmt _ _ ?ENV ?Fuel1 ?initialSt ?initialM ?s = ?final
        |- context [FlatImp.eval_stmt _ _ ?ENV ?Fuel2 ?initialSt ?initialM ?s] =>
          fuel_increasing_rewrite
      | |- context[match ?e with _ => _ end] =>
          destruct_one_match
      | |- context[FlatImp.eval_stmt _ _ _ (S ?f) _ _ _] =>
          progress simpl
      | H: ?f = S _ |- context[FlatImp.eval_stmt _ _ _ ?f _ _ _] =>
          rewrite H
                  (*
      | H: convert_bopname ?op = _
        |- context[Semantics.interp_binop ?op ?w ?w0] =>
          rewrite <- (eval_binop_compat op w w0); rewrite H

      | H: convert_bopname ?op = _ |- Some (put _ _ (_ ?w1 ?w2), _) = Some _ =>
          rewrite <- (eval_binop_compat op w1 w2); rewrite H
      | H: context [ get (put _ ?v _) ?v] |- _ =>
          rewrite get_put_same in H
*)
      end; cleanup_options; eauto); simpl;
      repeat (match goal with
      | |- context[if ?e then _ else _] =>
          destruct e
      | |- true = negb ?b =>
          let H' := fresh in
          pose proof (negb_true_iff b) as H'; destruct H' as [_ H'];
          symmetry; apply H'; simpl_reg_eqb
      | |- false = negb ?b =>
          let H' := fresh in
          pose proof (negb_false_iff b) as H'; destruct H' as [_ H'];
          symmetry; apply H'; simpl_reg_eqb
        end); auto.
   - inversion H0.
   - inversion H0.
  Qed.
  *)
  Admitted.

 Lemma flattenStmt_correct_aux:
    forall fuelH sH sL ngs ngs' (initialH finalH initialL: locals) initialM finalM,
    flattenStmt ngs sH = (sL, ngs') ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs) ->
    disjoint (ExprImp.modVars sH) (allFreshVars ngs) ->
    ExprImp.eval_cmd map.empty fuelH initialH initialM sH = Some (finalH, finalM) ->
    exists fuelL finalL,
      FlatImp.eval_stmt map.empty fuelL initialL initialM sL = Some (finalL, finalM) /\
      map.extends finalL finalH.
  Proof.
    induction fuelH; introv F Ex U Di Ev; [solve [inversionss] |].
  Admitted. (*
    ExprImp.invert_eval_cmd.
    - simpl in F. inversions F. destruct_pair_eqs.
      exists 1%nat initialL. auto.
    - repeat (inversionss; try destruct_one_match_hyp).
      pose proof flattenExpr_correct_aux as P.
      specialize (P empty_map) with (initialM := initialM) (1 := E) (2 := Ex) (3 := U) (4 := Ev0).
      destruct P as [fuelL [prefinalL [Evs G]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt _ _ empty_map SfuelL initialL initialM s = Some (prefinalL, initialM)) as Evs'. {
          eapply FlatImp.increase_fuel_still_Success; [|eassumption]. omega.
        }
        simpl in *.
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc.
    - simpl in F. inversions F. destruct_pair_eqs.
      exists 1%nat initialL. split. solve [auto]. subst.
      clear IHfuelH.
      state_calc.
    - repeat (inversionss; try destruct_one_match_hyp).
      match goal with
      | Ev: ExprImp.eval_expr _ _ = Some _ |- _ =>
        let P := fresh "P" in
        pose proof (flattenExpr_correct_aux empty_map) as P;
        specialize P with (initialM := initialM) (4 := Ev);
        specializes P; [ eassumption .. | ];
        let fuelL := fresh "fuelL" in
        let prefinalL := fresh "prefinalL" in
        destruct P as [fuelL [prefinalL P]];
        deep_destruct P
      end.
      match goal with
      | Ev: ExprImp.eval_expr _ _ = Some _ |- _ =>
        let P := fresh "P" in
        pose proof (flattenExpr_correct_aux empty_map) as P;
        specialize P with (initialL := prefinalL) (initialM := initialM) (4 := Ev)
      end.
      specializes P1.
      { eassumption. }
      { pose_flatten_var_ineqs. clear IHfuelH.
        state_calc. }
      { pose_flatten_var_ineqs. clear IHfuelH. state_calc. }
      destruct P1 as [fuelL2 P1]. deep_destruct P1.
      exists (S (S (S (fuelL + fuelL2)))). eexists.
      remember (S (S (fuelL + fuelL2))) as Sf.
      split.
      + simpl in *. fuel_increasing_rewrite. simpl. subst Sf.
        remember (S (fuelL + fuelL2)) as Sf. simpl. fuel_increasing_rewrite.
        subst Sf. simpl. rewrite_match.
        assert (get finalL v = Some av) as G. {
          clear IHfuelH. pose_flatten_var_ineqs. state_calc.
        }
        rewrite_match.
        reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc. (* TODO this takes more than a minute, which is annoying *)

    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose_flatten_var_ineqs.
      rename condition into condH, s into condL, s0 into sL1, s1 into sL2.

      pose proof (flattenBooleanExpr_correct_aux empty_map) as P.
      specialize P with (initialM := initialM)
                        (1 := E) (2 := Ex) (3 := U) (4 := Ev0).
      destruct P as [fuelLcond [initial2L [Evcond G]]].

      specialize IHfuelH with (initialL := initial2L) (1:= E0) (5:= Ev).
      destruct IHfuelH as [fuelL [finalL [evbranch Ex2]]].
      unfold FlatImp.accessedVarsBcond in *.
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := initial2L) (1 := E0) (5 := Ev).
      destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
      * state_calc.
      * state_calc.
      * simpl in Di. state_calc.
      * exists (S (S (fuelLcond + fuelL))). eexists.
        refine (conj _ Ex2).
        remember (S (fuelLcond + fuelL)) as f.
        simpl in *.
        fuel_increasing_rewrite.
        subst f.
        simpl. rewrite G. simpl.
        simpl_reg_eqb.
        assert (negb false = true) by auto. rewrite H.
        fuel_increasing_rewrite.
        reflexivity.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose_flatten_var_ineqs.
      rename condition into condH, s into condL, s0 into sL1, s1 into sL2.

      pose proof (flattenBooleanExpr_correct_aux empty_map) as P.
      specialize P with (initialM := initialM)
                        (1 := E) (2 := Ex) (3 := U) (4 := Ev0).
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := initial2L) (1 := E1) (5 := Ev).
      destruct IHfuelH as [fuelL [finalL [evbranch Ex2]]].
      unfold FlatImp.accessedVarsBcond in *.
      pose_flatten_var_ineqs.
      * state_calc.
      * state_calc.
      * simpl in Di. set_solver.
      * exists (S (S (fuelLcond + fuelL))). eexists.
        refine (conj _ Ex2).
        remember (S (fuelLcond + fuelL)) as tempFuel.
        simpl in *.
        fuel_increasing_rewrite.
        subst tempFuel.
        simpl. rewrite G. simpl.
        simpl_reg_eqb.
        assert (negb true = false) by auto. rewrite H.
        fuel_increasing_rewrite.
        reflexivity.

    - simpl in F. do 2 destruct_one_match_hyp. inversions F.
      pose proof IHfuelH as IHfuelH2.
      specializes IHfuelH.
      1: exact E. 1: exact Ex. 3: eassumption.
      { clear IHfuelH2. state_calc. }
      { simpl in Di. set_solver. }
      destruct IHfuelH as [fuelL1 [middleL [EvL1 Ex1]]].
      rename IHfuelH2 into IHfuelH.
      rename s into sL1, s0 into sL2.
      pose_flatten_var_ineqs.
      simpl in Di.
      pose proof ExprImp.modVarsSound as D1.
      specialize D1 with (1 := Ev0).
      specialize IHfuelH with (1 := E0) (2 := Ex1).
      specializes IHfuelH. 3: eassumption.
      { state_calc. }
      { state_calc. }
      destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
      exists (S (fuelL1 + fuelL2)) finalL.
      refine (conj _ Ex2).
      simpl in *.
      fuel_increasing_rewrite. fuel_increasing_rewrite. reflexivity.

    - simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.

      pose proof (flattenBooleanExpr_correct_aux empty_map) as P.
      specialize P with (initialM := initialM) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      pose_flatten_var_ineqs.

      specialize IHfuelH with (1 := E0) (5 := Ev2) as IH.
      specialize (IH initial2L).
      specializes IH; [clear IHfuelH .. |].
      { state_calc. }
      { state_calc. }
      { set_solver. }
      destruct IH as [fuelL1 [middleL [EvL1 Ex1]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := middleL) (1 := F0) (5 := Ev).
      specializes IHfuelH.
      { state_calc. }
      { pose proof ExprImp.modVarsSound as D1.
        specialize D1 with (1 := Ev2).
        state_calc. }
      { set_solver. }
      destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
      exists (S (fuelL1 + fuelL2 + fuelLcond)) finalL.
      refine (conj _ Ex2).
      simpl in *.
      fuel_increasing_rewrite.
      rewrite G. simpl. simpl_reg_eqb.
      fuel_increasing_rewrite.
      fuel_increasing_rewrite.
      reflexivity.
    - simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.

      pose proof (flattenBooleanExpr_correct_aux empty_map) as P.
      specialize P with (initialM := initialM) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      exists (S fuelLcond) initial2L.
      pose_flatten_var_ineqs.
      split; [|clear IHfuelH; state_calc].
      simpl in *.
      fuel_increasing_rewrite.
      rewrite G. simpl. simpl_reg_eqb. reflexivity.

    - rewrite empty_is_empty in Ev0. inversion Ev0.

    - clear -action actname_empty. rewrite actname_empty in action. destruct action.
  Qed.
  *)

  Definition ExprImp2FlatImp(s: Syntax.cmd): FlatImp.stmt :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_cmd s)) s).

  Context {varname_eq_dec: DecidableEq varname}. (* TODO *)

  Lemma flattenStmt_correct_fixpointsemantics: forall fuelH sH sL initialM finalH finalM,
    ExprImp2FlatImp sH = sL ->
    ExprImp.eval_cmd map.empty fuelH map.empty initialM sH = Some (finalH, finalM) ->
    exists fuelL finalL,
      FlatImp.eval_stmt map.empty fuelL map.empty initialM sL = Some (finalL, finalM) /\
      forall resVar res, map.get finalH resVar = Some res -> map.get finalL resVar = Some res.
  Proof.
    introv C EvH.
    unfold ExprImp2FlatImp, fst in C. destruct_one_match_hyp. subst s.
    pose proof flattenStmt_correct_aux as P.
    specialize P with (1 := E).
    specialize P with (4 := EvH).
    specialize P with (initialL := map.empty).
    destruct P as [fuelL [finalL [EvL ExtL]]].
    - unfold map.extends. auto.
    - unfold map.undef_on. repeat intro. rewrite map.get_empty. reflexivity.
    - unfold disjoint.
      intro x.
      pose proof (freshNameGenState_spec (ExprImp.allVars_cmd sH) x) as P.
      (* PARAMRECORDS ? : why do I have to give semantics_params explicitly? *)
      destruct (in_dec varname_eq_dec x (@ExprImp.allVars_cmd semantics_params sH)) as [Iyes | Ino].
      + auto.
      + left. clear -Ino actname_empty.
        intro. apply Ino.

        (* PARAMRECORDS *)
        Fail apply ExprImp.modVars_subset_allVars; assumption.
        pose proof ExprImp.modVars_subset_allVars as P; apply P; assumption.

    - exists fuelL finalL. apply (conj EvL).
      intros. state_calc.
  Qed.

  (* Just while ExprImp doesn't have metrics *)
  Definition addMetrics_post(postcond : trace -> mem -> locals -> Prop):
    trace -> mem -> locals -> FlatImp.FlatImp.metrics -> Prop :=
    fun t m l mc => postcond t m l.

  Lemma flattenStmt_correct: forall m sH sL post,
    ExprImp2FlatImp sH = sL ->
    exec map.empty sH nil m map.empty post ->
    exists mc,
    FlatImp.exec map.empty sL nil m map.empty mc (addMetrics_post post).
  Admitted.

End FlattenExpr.
