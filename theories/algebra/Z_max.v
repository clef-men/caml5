From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.

Record Z_max := {
  Z_max_car : Z
}.
Add Printing Constructor Z_max.

Canonical Z_max_O :=
  leibnizO Z_max.

Implicit Types n m : Z.
Implicit Types x y z : Z_max.

#[local] Instance Z_max_valid : Valid Z_max :=
  λ _,
    True.
#[local] Instance Z_max_validN : ValidN Z_max :=
  λ _ _,
    True.
#[local] Instance Z_max_pcore : PCore Z_max :=
  Some.
#[local] Instance Z_max_op : Op Z_max :=
  λ x1 x2,
    Build_Z_max (Z_max_car x1 `max` Z_max_car x2).

Lemma Z_max_op_eq n1 n2 :
  Build_Z_max n1 ⋅ Build_Z_max n2 = Build_Z_max (n1 `max` n2).
Proof.
  done.
Qed.

Lemma Z_max_included x1 x2 :
  x1 ≼ x2 ↔
  (Z_max_car x1 ≤ Z_max_car x2)%Z.
Proof.
  split.
  - intros [y ->]. simpl. lia.
  - exists x2. rewrite /op /Z_max_op Z.max_r; last lia. destruct x2. done.
Qed.

Lemma Z_max_ra_mixin :
  RAMixin Z_max.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !Z_max_op_eq Z.max_assoc //.
  - intros [] []. rewrite Z_max_op_eq Z.max_comm //.
  - intros []. rewrite Z_max_op_eq Z.max_id //.
Qed.
Canonical Z_max_R :=
  discreteR Z_max Z_max_ra_mixin.
#[global] Instance Z_max_cmra_discrete :
  CmraDiscrete Z_max_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

#[global] Instance Z_max_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma Z_max_local_update x y x' :
  (Z_max_car x ≤ Z_max_car x')%Z →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= ?.
  rewrite local_update_discrete. move=> [[p] |] _ /=; last done.
  rewrite !Z_max_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance Z_max_idemp :
  IdemP (=@{Z_max}) (⋅).
Proof.
  intros []. rewrite Z_max_op_eq. f_equal. lia.
Qed.

#[global] Instance Z_max_is_op n1 n2 :
  IsOp (Build_Z_max (n1 `max` n2)) (Build_Z_max n1) (Build_Z_max n2).
Proof.
  done.
Qed.
