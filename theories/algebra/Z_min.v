From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.

Record Z_min := {
  Z_min_car : Z
}.
Add Printing Constructor Z_min.

Canonical Z_min_O :=
  leibnizO Z_min.

Implicit Types n m : Z.
Implicit Types x y z : Z_min.

#[local] Instance Z_min_valid : Valid Z_min :=
  λ _,
    True.
#[local] Instance Z_min_validN : ValidN Z_min :=
  λ _ _,
    True.
#[local] Instance Z_min_pcore : PCore Z_min :=
  Some.
#[local] Instance Z_min_op : Op Z_min :=
  λ x1 x2,
    Build_Z_min (Z_min_car x1 `min` Z_min_car x2).

Lemma Z_min_op_eq n1 n2 :
  Build_Z_min n1 ⋅ Build_Z_min n2 = Build_Z_min (n1 `min` n2).
Proof.
  done.
Qed.

Lemma Z_min_included x1 x2 :
  x1 ≼ x2 ↔
  (Z_min_car x2 ≤ Z_min_car x1)%Z.
Proof.
  split.
  - intros [y ->]. simpl. lia.
  - exists x2. rewrite /op /Z_min_op Z.min_r; last lia. destruct x2. done.
Qed.

Lemma Z_min_ra_mixin :
  RAMixin Z_min.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !Z_min_op_eq Z.min_assoc //.
  - intros [] []. rewrite Z_min_op_eq Z.min_comm //.
  - intros []. rewrite Z_min_op_eq Z.min_id //.
Qed.
Canonical Z_min_R :=
  discreteR Z_min Z_min_ra_mixin.
#[global] Instance Z_min_cmra_discrete :
  CmraDiscrete Z_min_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

#[global] Instance Z_min_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma Z_min_local_update x y x' :
  (Z_min_car x' ≤ Z_min_car x)%Z →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= ?.
  rewrite local_update_discrete. move=> [[p] |] _ /=; last done.
  rewrite !Z_min_op_eq => [= ?].
  split; first done. f_equal. lia.
Qed.

#[global] Instance Z_min_idemp :
  IdemP (=@{Z_min}) (⋅).
Proof.
  intros []. rewrite Z_min_op_eq. f_equal. lia.
Qed.

#[global] Instance Z_min_is_op n1 n2 :
  IsOp (Build_Z_min (n1 `min` n2)) (Build_Z_min n1) (Build_Z_min n2).
Proof.
  done.
Qed.
