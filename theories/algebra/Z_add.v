From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.

Record Z_add := {
  Z_add_car : Z ;
}.
Add Printing Constructor Z_add.

Canonical Z_add_O :=
  leibnizO Z_add.

Implicit Types n m : Z.
Implicit Types x y z : Z_add.

#[local] Instance Z_add_valid : Valid Z_add :=
  λ _,
    True.
#[local] Instance Z_add_validN : ValidN Z_add :=
  λ _ _,
    True.
#[local] Instance Z_add_pcore : PCore Z_add :=
  λ x,
    Some (Build_Z_add 0).
#[local] Instance Z_add_op : Op Z_add :=
  λ x1 x2,
    Build_Z_add (Z_add_car x1 + Z_add_car x2).
#[local] Instance Z_add_unit : Unit Z_add :=
  Build_Z_add 0.

Lemma Z_add_op_eq n1 n2 :
  Build_Z_add n1 ⋅ Build_Z_add n2 = Build_Z_add (n1 + n2).
Proof.
  done.
Qed.

Lemma Z_add_ra_mixin :
  RAMixin Z_add.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !Z_add_op_eq Z.add_assoc //.
  - intros [] []. rewrite Z_add_op_eq Z.add_comm //.
  - intros []. rewrite Z_add_op_eq //.
  - intros [] []. exists (Build_Z_add 0). done.
Qed.
Canonical Z_add_R :=
  discreteR Z_add Z_add_ra_mixin.
#[global] Instance Z_add_cmra_discrete :
  CmraDiscrete Z_add_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

Lemma Z_add_ucmra_mixin :
  UcmraMixin Z_add.
Proof.
  split; try done. intros []. done.
Qed.
Canonical Z_add_UR :=
  Ucmra Z_add Z_add_ucmra_mixin.

#[global] Instance Z_add_cancelable x :
  Cancelable x.
Proof.
  intros ? [] [] _. destruct x.
  rewrite !Z_add_op_eq => [=].
  rewrite Z.add_cancel_l => -> //.
Qed.

Lemma Z_add_local_update x1 y1 x2 y2 :
  (Z_add_car x1 + Z_add_car y2 = Z_add_car x2 + Z_add_car y1)%Z →
  (x1, y1) ~l~> (x2, y2).
Proof.
  move: x1 y1 x2 y2 => [n1] [m1] [n2] [m2] /= ?.
  rewrite local_update_unital_discrete => [[p]] _.
  rewrite !Z_add_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance Z_add_is_op n1 n2 :
  IsOp (Build_Z_add (n1 + n2)) (Build_Z_add n1) (Build_Z_add n2).
Proof.
  done.
Qed.
