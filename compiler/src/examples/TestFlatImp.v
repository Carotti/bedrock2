Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.MinimalLogging.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.Memory.
Require Import compiler.Decidable.
Require Import riscv.util.BitWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import riscv.MachineWidth32.


Definition var: Set := Z. (* only inside this test module *)
Definition func: Set := Z.
Notation stmt := (stmt var func).

Definition _n := 0%Z.
Definition _a := 1%Z.
Definition _b := 2%Z.
Definition _s := 3%Z.
Definition _one := 4%Z.
(*
one = 1
n = input()
a = 0
b = 1
loop:
  stay in loop only if n nonzero
  s = a+b
  a = b
  b = s
  n = n - one
 *)


Example fib(n: Z): stmt  :=
  SSeq (SLit _one 1) (
  SSeq (SLit _n n) (
  SSeq (SLit _a 0) (
  SSeq (SLit _b 1) (
  SLoop SSkip
        _n
        (SSeq (SOp _s bopname.add _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n bopname.sub _n _one)))))
  )))).

Definition annoying_eq: DecidableEq
  (list var * list func * stmt). Admitted.
Existing Instance annoying_eq.

Definition eval_stmt_test fuel initialSt := @eval_stmt (word 32) _ _ _ _ (List_Map _ _) empty_map fuel initialSt no_mem.

Example finalFibState(n: Z) := (eval_stmt_test 100 empty_map (fib n)).
Example finalFibVal(n: Z): option (word 32) := match finalFibState n with
| Some (s, _) => get s _b
| _ => None
end.

Goal finalFibVal 0 = Some (ZToWord 32  1). reflexivity. Qed.
Goal finalFibVal 1 = Some (ZToWord 32  1). reflexivity. Qed.
Goal finalFibVal 2 = Some (ZToWord 32  2). reflexivity. Qed.
Goal finalFibVal 3 = Some (ZToWord 32  3). reflexivity. Qed.
Goal finalFibVal 4 = Some (ZToWord 32  5). reflexivity. Qed.
Goal finalFibVal 5 = Some (ZToWord 32  8). reflexivity. Qed.
Goal finalFibVal 6 = Some (ZToWord 32 13). reflexivity. Qed.

Definition eval_stmt_log_test fuel initialSt := @eval_stmt_log (word 32) _ _ _ _ (List_Map _ _) empty_map fuel initialSt EmptyMetricLog no_mem.

Example finalFibLogState(n: Z) := (eval_stmt_log_test 100 empty_map (fib n)).

Example finalFibLogVal(n: Z) : option (word 32) := match finalFibLogState n with
| Some (s, _, _) => get s _b
| _ => None
end.

Example finalFibLogMetrics(n: Z) := match finalFibLogState n with
| Some (_, log, _) => log
| _ => EmptyMetricLog
end.

Goal finalFibLogVal 0 = Some (ZToWord 32  1). reflexivity. Qed.
Goal finalFibLogVal 1 = Some (ZToWord 32  1). reflexivity. Qed.
Goal finalFibLogVal 2 = Some (ZToWord 32  2). reflexivity. Qed.
Goal finalFibLogVal 3 = Some (ZToWord 32  3). reflexivity. Qed.
Goal finalFibLogVal 4 = Some (ZToWord 32  5). reflexivity. Qed.
Goal finalFibLogVal 5 = Some (ZToWord 32  8). reflexivity. Qed.
Goal finalFibLogVal 6 = Some (ZToWord 32 13). reflexivity. Qed.

Eval cbv in (finalFibLogMetrics 10).
