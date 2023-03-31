From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.common Require Export
  natinf.
From caml5.algebra Require Export
  base.

Record natinf_min := {
  natinf_min_car : natinf ;
}.
Add Printing Constructor natinf_min.

Canonical natinf_min_O :=
  leibnizO natinf_min.

Implicit Types n m : natinf.
Implicit Types x y : natinf_min.

#[local] Instance natinf_min_valid : Valid natinf_min :=
  λ _,
    True.
#[local] Instance natinf_min_validN : ValidN natinf_min :=
  λ _ _,
    True.
#[local] Instance natinf_min_pcore : PCore natinf_min :=
  Some.
#[local] Instance natinf_min_op : Op natinf_min :=
  λ x1 x2,
    Build_natinf_min (natinf.natinf_min (natinf_min_car x1) (natinf_min_car x2)).
#[local] Instance natinf_min_unit : Unit natinf_min :=
  Build_natinf_min natinf_inf.

Lemma natinf_min_op_eq n1 n2 :
  Build_natinf_min n1 ⋅ Build_natinf_min n2 = Build_natinf_min (natinf.natinf_min n1 n2).
Proof.
  done.
Qed.

Lemma natinf_min_included x1 x2 :
  x1 ≼ x2 ↔
  natinf_le (natinf_min_car x2) (natinf_min_car x1).
Proof.
  split.
  - intros [y ->]. apply natinf_le_min_1.
  - exists x2. rewrite /op /natinf_min_op natinf_min_r; first destruct x2; done.
Qed.

Lemma natinf_min_ra_mixin :
  RAMixin natinf_min.
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [] [] []. rewrite !natinf_min_op_eq assoc //.
  - intros [] []. rewrite natinf_min_op_eq (comm natinf.natinf_min) //.
  - intros []. rewrite natinf_min_op_eq idemp //.
Qed.
Canonical natinf_min_R :=
  discreteR natinf_min natinf_min_ra_mixin.
#[global] Instance natinf_min_cmra_discrete :
  CmraDiscrete natinf_min_R.
Proof.
  apply discrete_cmra_discrete.
Qed.

Lemma natinf_min_ucmra_mixin :
  UcmraMixin natinf_min.
Proof.
  split; try done.
  intros []. rewrite /op /natinf_min_op. f_equal.
Qed.
Canonical natinf_min_UR :=
  Ucmra natinf_min natinf_min_ucmra_mixin.

#[global] Instance max_natinf_core_id x :
  CoreId x.
Proof.
  constructor. done.
Qed.

Lemma natinf_min_local_update x y x' :
  natinf_le (natinf_min_car x') (natinf_min_car x) →
  (x, y) ~l~> (x', x').
Proof.
  move: x y x' => [n] [m] [n'] /= Hle.
  rewrite local_update_unital_discrete => [[p]] _.
  rewrite !natinf_min_op_eq => [= ?].
  split; first done. f_equal.
  destruct (natinf_min_case m p); simplify_eq;
    rewrite natinf_le_iff_min in Hle;
    rewrite -Hle -!assoc idemp //.
Qed.

#[global] Instance natinf_min_0_l :
  LeftAbsorb (=) (Build_natinf_min (natinf_nat 0)) (⋅).
Proof.
  intros [x]. rewrite natinf_min_op_eq left_absorb //.
Qed.
#[global] Instance natinf_min_inf_r :
  RightAbsorb (=) (Build_natinf_min (natinf_nat 0)) (⋅).
Proof.
  intros [x]. rewrite natinf_min_op_eq right_absorb //.
Qed.

#[global] Instance natinf_min_op_idemp :
  IdemP (=@{natinf_min}) (⋅).
Proof.
  intros []. rewrite natinf_min_op_eq. f_equal. rewrite idemp //.
Qed.

#[global] Instance natinf_min_is_op n1 n2 :
  IsOp (Build_natinf_min (natinf.natinf_min n1 n2)) (Build_natinf_min n1) (Build_natinf_min n2).
Proof.
  done.
Qed.
