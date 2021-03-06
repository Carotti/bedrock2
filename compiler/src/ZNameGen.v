Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import compiler.NameGen.


Definition listmax(l: list nat): nat := fold_right max 0 l.

Lemma listmax_spec: forall l v, In v l -> v <= listmax l.
Proof.
  induction l; intros.
  - simpl in H. contradiction.
  - simpl in *. destruct H.
    + subst. apply Nat.le_max_l.
    + pose proof (Nat.le_max_r a (listmax l)).
      specialize (IHl v H).
      eapply Nat.le_trans; eassumption.
Qed.

Local Open Scope Z_scope.

Definition listmaxZ(l: list Z): Z := fold_right Z.max 0 l.

Lemma listmaxZ_spec: forall l v, In v l -> v <= listmaxZ l.
Proof.
  induction l; intros.
  - simpl in H. contradiction.
  - simpl in *. destruct H.
    + subst. apply Z.le_max_l.
    + pose proof (Z.le_max_r a (listmaxZ l)).
      specialize (IHl v H).
      eapply Z.le_trans; eassumption.
Qed.

Local Set Refine Instance Mode.

Unset Universe Minimization ToSet.

Instance ZNameGen: NameGen Z Z := {
  freshNameGenState := fun l => listmaxZ l + 1;
  genFresh s := (s, s + 1);
  allFreshVars s := fun x => (s <= x)
}.
- abstract (intros; repeat autounfold with unf_basic_set_defs unf_derived_set_defs;
            inversion H; subst; clear H; intuition omega).
- abstract (intros; repeat autounfold with unf_basic_set_defs unf_derived_set_defs;
            apply listmaxZ_spec in H; omega).
Defined.
