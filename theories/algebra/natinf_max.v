From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.common Require Export
  natinf.
From caml5.algebra Require Export
  base.

Record natinf_max := {
  natinf_max_car : natinf ;
}.
Add Printing Constructor natinf_max.

Canonical natinf_max_O :=
  leibnizO natinf_max.

Implicit Types n m : natinf.
Implicit Types x y : natinf_max.

#[local] Instance natinf_max_valid : Valid natinf_max :=
  λ _,
    True.
#[local] Instance natinf_max_validN : ValidN natinf_max :=
  λ _ _,
    True.
#[local] Instance natinf_max_pcore : PCore natinf_max :=
  Some.
#[local] Instance natinf_max_op : Op natinf_max :=
  λ x1 x2,
    Build_natinf_max (natinf.natinf_max (natinf_max_car x1) (natinf_max_car x2)).
#[local] Instance natinf_max_unit : Unit natinf_max :=
  Build_natinf_max (natinf_nat 0).

Lemma natinf_max_op_eq n1 n2 :
  Build_natinf_max n1 ⋅ Build_natinf_max n2 = Build_natinf_max (natinf.natinf_max n1 n2).
Proof.
  done.
Qed.

Lemma natinf_max_included x1 x2 :
  x1 ≼ x2 ↔
  natinf_le (natinf_max_car x1) (natinf_max_car x2).
Proof.
  split.
  - intros [y ->]. apply natinf_le_max_1.
  - exists x2. rewrite /op /natinf_max_op natinf_max_r; first destruct x2; done.
Qed.

Lemma natinf_max_ra_mixin :
  RAMixin natinf_max.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !natinf_max_op_eq assoc //.
  - intros [] []. rewrite natinf_max_op_eq (comm natinf.natinf_max) //.
  - intros []. rewrite natinf_max_op_eq idemp //.
Qed.
Canonical natinf_max_R :=
  discreteR natinf_max natinf_max_ra_mixin.
#[global] Instance natinf_max_cmra_discrete :
  CmraDiscrete natinf_max_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

Lemma natinf_max_ucmra_mixin :
  UcmraMixin natinf_max.
Proof.
  split; try done.
  intros []. rewrite /op /natinf_max_op. f_equal. apply left_id, _.
Qed.
Canonical natinf_max_UR :=
  Ucmra natinf_max natinf_max_ucmra_mixin.

#[global] Instance max_natinf_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma natinf_max_local_update x y x' :
  natinf_le (natinf_max_car x) (natinf_max_car x') →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= Hle.
  rewrite local_update_unital_discrete => [[p]] _.
  rewrite !natinf_max_op_eq => [= ?].
  split; first done. f_equal.
  destruct (natinf_min_case m p); simplify_eq;
    rewrite natinf_le_iff_max in Hle;
    rewrite -Hle (comm _ _ n') -!assoc idemp //.
Qed.

#[global] Instance natinf_max_inf_l :
  LeftAbsorb (=) (Build_natinf_max natinf_inf) (⋅).
Proof.
  done.
Qed.
#[global] Instance natinf_max_inf_r :
  RightAbsorb (=) (Build_natinf_max natinf_inf) (⋅).
Proof.
  intros [x]. rewrite natinf_max_op_eq right_absorb //.
Qed.

#[global] Instance natinf_max_op_idemp :
  IdemP (=@{natinf_max}) (⋅).
Proof.
  intros []. rewrite natinf_max_op_eq. f_equal. rewrite idemp //.
Qed.

#[global] Instance natinf_max_is_op n1 n2 :
  IsOp (Build_natinf_max (natinf.natinf_max n1 n2)) (Build_natinf_max n1) (Build_natinf_max n2).
Proof.
  done.
Qed.
