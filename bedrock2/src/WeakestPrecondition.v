Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Notations coqutil.Map.Interface.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Definition literal v (post : _ -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : varname) (post : word -> Prop) : Prop :=
    bind_ex_Some v <- map.get l x; post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    bind_ex_Some v <- load s m a; post v.
  Definition store sz m a v post :=
    bind_ex_Some m <- store sz m a v; post m.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (e : Syntax.expr) (post : word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v post
      | expr.var x =>
        get l x post
      | expr.op op e1 e2 =>
        rec e1 (fun v1 =>
        rec e2 (fun v2 =>
        post (interp_binop op v1 v2)))
      | expr.load s e =>
        rec e (fun a =>
        load s m a post)
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Section WithFunctions.
    Context (call : funname -> trace -> mem -> list word -> metrics -> (trace -> mem -> list word -> metrics -> Prop) -> Prop).
    Definition dexpr m l e v := expr m l e (eq v).
    Definition dexprs m l es vs := list_map (expr m l) es (eq vs).
    Definition cmd_body (rec:_->_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals) (mc : metrics)
             (post : trace -> mem -> locals -> metrics -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l mc
      | cmd.set x ev =>
        bind_ex v <- dexpr m l ev;
        dlet! l := map.put l x v in
        post t m l mc
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l mc
      | cmd.store sz ea ev =>
        bind_ex a <- dexpr m l ea;
        bind_ex v <- dexpr m l ev;
        store sz m a v (fun m =>
        post t m l mc)
      | cmd.cond br ct cf =>
        bind_ex v <- dexpr m l br;
        (word.unsigned v <> 0%Z -> rec ct t m l mc post) /\
        (word.unsigned v = 0%Z -> rec cf t m l mc post)
      | cmd.seq c1 c2 =>
        rec c1 t m l mc (fun t m l mc => rec c2 t m l mc post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          bind_ex b <- dexpr m l e;
          (word.unsigned b <> 0%Z -> rec c t m l mc (fun t' m l mc =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l mc))
      | cmd.call binds fname arges =>
        bind_ex args <- dexprs m l arges;
        call fname t m args mc (fun t m rets mc =>
          bind_ex_Some l <- map.putmany_of_list binds rets l;
          post t m l mc)
      | cmd.interact binds action arges =>
        bind_ex args <- dexprs m l arges;
        ext_spec t m action args (let old_mem := m in fun m rets =>
          bind_ex_Some l <- map.putmany_of_list binds rets l;
          post (cons ((old_mem, action, args), (m, rets)) t) m l mc)
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : trace) (m : mem) (mc : metrics) (args : list word) (post : trace -> mem -> list word -> metrics -> Prop) :=
      bind_ex_Some l <- map.of_list innames args;
      cmd call c t m l mc (fun t m l mc =>
        list_map (get l) outnames (fun rets =>
        post t m rets mc)).

  Definition call_body rec (functions : list (funname * (list varname * list varname * cmd.cmd)))
                (fname : funname) (t : trace) (m : mem) (args : list word) (mc : metrics)
                (post : trace -> mem -> list word -> metrics -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if funname_eqb f fname
      then func (rec functions) decl t m mc args post
      else rec functions fname t m args mc post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l mc post : Prop := cmd (call funcs) main t m l mc post.
End WeakestPrecondition.

Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?params ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body params CA (@cmd params CA) c t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?params ?m ?l ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body params m l (@expr params m l) arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_call e :=
  lazymatch e with
    @call ?params ?fs ?fname ?t ?m ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body params (@call params) fs fname t m l post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.