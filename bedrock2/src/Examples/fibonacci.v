Require Import coqutil.Z.div_mod_to_equations.
Require Import bedrock2.BasicCSyntax bedrock2.NotationsInConstr.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Interface.
Import Syntax BinInt String List.ListNotations.
Require Import coqutil.Z.Lia.
From coqutil.Map Require SortedListWord SortedListString Z_keyed_SortedListMap Empty_set_keyed_map.
From coqutil Require Import Word.Interface Word.Naive Z.HexNotation String.
Require Import bedrock2.Semantics.
Import List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Local Instance syntax_parameters : Syntax.parameters := {|
  varname := Z;
  funname := String.string;
  actname := Empty_set;
|}.

Local Instance semantics_parameters : Semantics.parameters := (
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  width := 32;
  syntax := syntax_parameters;
  mem := SortedListWord.map _ _;
  locals := Z_keyed_SortedListMap.Zkeyed_map _;
  funname_env := SortedListString.map;
  funname_eqb := String.eqb;
  ext_spec t mGive action args post := False;
  |}).

Local Coercion var {p} (x : @varname p) : expr := expr.var x. (* COQBUG(4593) *)
Local Coercion literal (x : Z) : expr := expr.literal x.

Definition fibonacci :=
  let a := 2 in
  let b := 3 in
  let c := 4 in
  let i := 5 in
  let n := 6 in
  ("fibonacci", ([n], [b], bedrock_func_body:(
    a = 0;;
    b = 1;;
    i = 0;;
    while (i < n) {{
      c = a + b;;
      a = b;;
      b = c;;
      i = i + 1
    }}
  ))).

From bedrock2 Require Import Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.

Fixpoint fib (n: nat): Z :=
  match n with
  | O => 0
  | S x =>
    match x with
    | O => 1
    | S y => (fib x + fib y)
    end
  end.

Instance spec_of_fibonacci : spec_of "fibonacci" := fun functions =>
  forall n_arg t m,
    @WeakestPrecondition.call semantics_parameters functions
      "fibonacci" t m [n_arg]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v] /\ (
        word.unsigned v = (fib (Z.to_nat (word.unsigned n_arg))))).

Local Instance mapok: coqutil.Map.Interface.map.ok mem := SortedListWord.ok (Naive.word 32 eq_refl) _.
Local Instance wordok: coqutil.Word.Interface.word.ok Semantics.word := coqutil.Word.Naive.ok _ _.
Local Instance byteok: coqutil.Word.Interface.word.ok Semantics.byte := coqutil.Word.Naive.ok _ _.

Lemma fibonacci_ok : program_logic_goal_for_function! fibonacci.
Proof.
    
  straightline.
  straightline.
  straightline.


  set (a := 2) in *.
  set (b := 3) in *.
  set (c' := 4) in *.
  set (i := 5) in *.
  set (n := 6) in *.

  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.

  refine (TailRecursion.tailrec (p := semantics_parameters)
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) [a;b;c';i;n]
    (fun v t m e ret x => _)
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      letexists; split; [repeat straightline|]. (* if condition evaluation *)
      split. (* if cases, path-blasting *)
      {
        repeat (straightline || (split; trivial; [])). all:t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          erewrite Z.land_1_r in *; change (2^1) with 2 in *.
          eapply Z.mod2_nonzero in Hbit.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul.
          unfold word.wrap.
          rewrite ?Z.mul_mod_idemp_l by discriminate.
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.pow_add_r by (pose proof word.unsigned_range x0; Z.div_mod_to_equations; blia).
          rewrite ?Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. } }
      { 
        repeat (straightline || (split; trivial; [])).
        all: t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          rewrite Z.land_1_r in *; change (2^1) with 2 in *.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul, ?Z.mul_mod_idemp_l by discriminate.
          cbv [word.wrap].
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.add_0_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. } } }
    { (* postcondition *) rewrite H, Z.pow_0_r, Z.mul_1_r, word.wrap_unsigned; auto. } }

  repeat straightline.

  repeat (split || letexists || t || trivial).
  setoid_rewrite H1; setoid_rewrite Z.mul_1_l; trivial.
Defined.


     change 2 with a;
     change 3 with b;
     change 4 with c;
     change 5 with i;
     change 6 with n.

       
   refine (
        let a := 2 in
        let b := 3 in
        let c := 4 in
        let i := 5 in
        let n := 6 in
  _).