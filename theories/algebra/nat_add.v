From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.

Record nat_add := {
  nat_add_car : nat ;
}.
Add Printing Constructor nat_add.

Canonical nat_add_O :=
  leibnizO nat_add.

Implicit Types n m : nat.
Implicit Types x y z : nat_add.

#[local] Instance nat_add_valid : Valid nat_add :=
  λ _,
    True.
#[local] Instance nat_add_validN : ValidN nat_add :=
  λ _ _,
    True.
#[local] Instance nat_add_pcore : PCore nat_add :=
  λ _,
    Some (Build_nat_add 0).
#[local] Instance nat_add_op : Op nat_add :=
  λ x1 x2,
    Build_nat_add (nat_add_car x1 + nat_add_car x2).
#[local] Instance nat_unit : Unit nat_add :=
  Build_nat_add 0.

Lemma nat_add_op_eq n1 n2 :
  Build_nat_add n1 ⋅ Build_nat_add n2 = Build_nat_add (n1 + n2).
Proof.
  done.
Qed.

Lemma nat_add_included x1 x2 :
  x1 ≼ x2 ↔
  nat_add_car x1 ≤ nat_add_car x2.
Proof.
  split.
  - intros (? & ->). simpl. lia.
  - destruct x1, x2. simpl.
    rewrite Nat.le_sum => [[y ->]].
    exists (Build_nat_add y). done.
Qed.

Lemma nat_add_ra_mixin :
  RAMixin nat_add.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !nat_add_op_eq Nat.add_assoc //.
  - intros [] []. rewrite nat_add_op_eq Nat.add_comm //.
  - intros []. rewrite nat_add_op_eq //.
  - intros [] []. exists (Build_nat_add 0). done.
Qed.
Canonical nat_add_R :=
  discreteR nat_add nat_add_ra_mixin.
#[global] Instance nat_add_cmra_discrete :
  CmraDiscrete nat_add_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

Lemma nat_add_ucmra_mixin :
  UcmraMixin nat_add.
Proof.
  split; try done. intros []. done.
Qed.
Canonical nat_add_UR :=
  Ucmra nat_add nat_add_ucmra_mixin.

#[global] Instance nat_add_cancelable x :
  Cancelable x.
Proof.
  intros ? [] [] _. destruct x.
  rewrite !nat_add_op_eq => [=].
  rewrite Nat.add_cancel_l => -> //.
Qed.

Lemma nat_add_local_update x1 y1 x2 y2 :
  nat_add_car x1 + nat_add_car y2 = nat_add_car x2 + nat_add_car y1 →
  (x1, y1) ~l~> (x2, y2).
Proof.
  move: x1 y1 x2 y2 => [n1] [m1] [n2] [m2] /= ?.
  rewrite local_update_unital_discrete => [[p]] _.
  rewrite !nat_add_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance nat_add_is_op n1 n2 :
  IsOp (Build_nat_add (n1 + n2)) (Build_nat_add n1) (Build_nat_add n2).
Proof.
  done.
Qed.
