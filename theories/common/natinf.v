From caml5 Require Import
  prelude.

Inductive natinf : Set :=
  | natinf_inf : natinf
  | natinf_nat : nat -> natinf.

Implicit Types n m : nat.
Implicit Types x y : natinf.

Definition natinf_add x1 x2 :=
  match x1 with
  | natinf_inf =>
      natinf_inf
  | natinf_nat n1 =>
      match x2 with
      | natinf_inf => natinf_inf
      | natinf_nat n2 => natinf_nat (n1 + n2)
      end
  end.

Definition natinf_min x1 x2 :=
  match x1 with
  | natinf_inf =>
      x2
  | natinf_nat n1 =>
      match x2 with
      | natinf_inf => x1
      | natinf_nat n2 => natinf_nat (n1 `min` n2)
      end
  end.
Definition natinf_max x1 x2 :=
  match x1 with
  | natinf_inf =>
      x1
  | natinf_nat n1 =>
      match x2 with
      | natinf_inf => x2
      | natinf_nat n2 => natinf_nat (n1 `max` n2)
      end
  end.

Definition natinf_le x1 x2 :=
  natinf_min x1 x2 = x1.
Definition natinf_ge x1 x2 :=
  natinf_le x2 x1.

#[global] Instance natinf_nat_inj :
  Inj (=) (=) natinf_nat.
Proof.
  intros ? ? [=]. done.
Qed.

Section natinf_add.
  #[global] Instance natinf_add_comm :
    Comm (=) natinf_add.
  Proof.
    intros [| n1] [| n2]; try done. simpl. f_equal. lia.
  Qed.
  #[global] Instance natinf_add_assoc :
    Assoc (=) natinf_add.
  Proof.
    intros [] [] []; try done. simpl. f_equal. lia.
  Qed.

  #[global] Instance natinf_add_inf_l :
    LeftAbsorb (=) natinf_inf natinf_add.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_add_inf_r :
    RightAbsorb (=) natinf_inf natinf_add.
  Proof.
    intros []; done.
  Qed.

  #[global] Instance natinf_add_0_l :
    LeftId (=) (natinf_nat 0) natinf_add.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_add_0_r :
    RightId (=) (natinf_nat 0) natinf_add.
  Proof.
    intros []; first done. simpl. f_equal. lia.
  Qed.

  Lemma natinf_add_eq_inf x1 x2 :
    natinf_add x1 x2 = natinf_inf →
    x1 = natinf_inf ∨ x2 = natinf_inf.
  Proof.
    destruct x1, x2; naive_solver.
  Qed.
  Lemma nating_add_eq_nat x1 x2 n :
    natinf_add x1 x2 = natinf_nat n →
      ∃ n1 n2,
      x1 = natinf_nat n1 ∧
      x2 = natinf_nat n2 ∧
      n = n1 + n2.
  Proof.
    destruct x1, x2; naive_solver.
  Qed.
End natinf_add.

Lemma natinf_min_max_case x1 x2 :
  natinf_min x1 x2 = x1 ∧ natinf_max x1 x2 = x2 ∨
  natinf_min x1 x2 = x2 ∧ natinf_max x1 x2 = x1.
Proof.
  destruct x1 as [| n1], x2 as [| n2]; try naive_solver.
  rewrite /=. apply Nat.min_case_strong; intros.
  - rewrite Nat.max_r; first done. naive_solver.
  - rewrite Nat.max_l; first done. naive_solver.
Qed.
Lemma natinf_min_iff_max x1 x2 :
  natinf_min x1 x2 = x1 ↔ natinf_max x1 x2 = x2.
Proof.
  split; destruct (natinf_min_max_case x1 x2) as [(-> & ->) | (-> & ->)]; naive_solver.
Qed.

Section natinf_min.
  #[global] Instance natinf_min_idemp :
    IdemP (=) natinf_min.
  Proof.
    intros []; [done | rewrite /= Nat.min_id //].
  Qed.
  #[global] Instance natinf_min_comm :
    Comm (=) natinf_min.
  Proof.
    intros [] []; try done. simpl. f_equal. lia.
  Qed.
  #[global] Instance natinf_min_assoc :
    Assoc (=) natinf_min.
  Proof.
    intros [] [] []; try done. simpl. f_equal. lia.
  Qed.

  #[global] Instance natinf_min_inf_l :
    LeftId (=) natinf_inf natinf_min.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_min_inf_r :
    RightId (=) natinf_inf natinf_min.
  Proof.
    intros []; done.
  Qed.

  #[global] Instance natinf_min_0_l :
    LeftAbsorb (=) (natinf_nat 0) natinf_min.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_min_0_r :
    RightAbsorb (=) (natinf_nat 0) natinf_min.
  Proof.
    intros []; [done | rewrite /= Nat.min_0_r //].
  Qed.

  Lemma natinf_min_case x1 x2 :
    natinf_min x1 x2 = x1 ∨ natinf_min x1 x2 = x2.
  Proof.
    destruct x1 as [| n1], x2 as [| n2]; simpl; auto.
    apply Nat.min_case; eauto.
  Qed.
  Lemma natinf_min_eq_inf x1 x2 :
    natinf_min x1 x2 = natinf_inf →
    x1 = natinf_inf ∧ x2 = natinf_inf.
  Proof.
    destruct x1, x2; done.
  Qed.

  Lemma natinf_le_iff_min x1 x2 :
    natinf_le x1 x2 ↔
    natinf_min x1 x2 = x1.
  Proof.
    done.
  Qed.
  Lemma natinf_ge_iff_min x1 x2 :
    natinf_ge x1 x2 ↔
    natinf_min x1 x2 = x2.
  Proof.
    rewrite (comm natinf_min) //.
  Qed.
  Lemma natinf_min_l x1 x2 :
    natinf_le x1 x2 →
    natinf_min x1 x2 = x1.
  Proof.
    done.
  Qed.
  Lemma natinf_min_r x1 x2 :
    natinf_le x2 x1 →
    natinf_min x1 x2 = x2.
  Proof.
    rewrite (comm natinf_min) //.
  Qed.
End natinf_min.

Section natinf_max.
  #[global] Instance natinf_max_idemp :
    IdemP (=) natinf_max.
  Proof.
    intros []; [done | rewrite /= Nat.max_id //].
  Qed.
  #[global] Instance natinf_max_comm :
    Comm (=) natinf_max.
  Proof.
    intros [] []; try done. simpl. f_equal. lia.
  Qed.
  #[global] Instance natinf_max_assoc :
    Assoc (=) natinf_max.
  Proof.
    intros [] [] []; try done. simpl. f_equal. lia.
  Qed.

  #[global] Instance natinf_max_inf_l :
    LeftAbsorb (=) natinf_inf natinf_max.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_max_inf_r :
    RightAbsorb (=) natinf_inf natinf_max.
  Proof.
    intros []; done.
  Qed.

  #[global] Instance natinf_max_0_l :
    LeftId (=) (natinf_nat 0) natinf_max.
  Proof.
    intros []; done.
  Qed.
  #[global] Instance natinf_max_0_r :
    RightId (=) (natinf_nat 0) natinf_max.
  Proof.
    intros []; [done | rewrite /= Nat.max_0_r //].
  Qed.

  Lemma natinf_max_case x1 x2 :
    natinf_max x1 x2 = x1 ∨ natinf_max x1 x2 = x2.
  Proof.
    destruct x1 as [| n1], x2 as [| n2]; simpl; auto.
    apply Nat.max_case; eauto.
  Qed.
  Lemma natinf_max_eq_nat x1 x2 n :
    natinf_max x1 x2 = natinf_nat n →
      ∃ n1 n2,
      x1 = natinf_nat n1 ∧
      x2 = natinf_nat n2 ∧
      n = n1 `max` n2.
  Proof.
    destruct x1, x2; naive_solver.
  Qed.

  Lemma natinf_le_iff_max x1 x2 :
    natinf_le x1 x2 ↔
    natinf_max x1 x2 = x2.
  Proof.
    setoid_rewrite natinf_min_iff_max. rewrite (comm natinf_max) //.
  Qed.
  Lemma natinf_ge_iff_max x1 x2 :
    natinf_ge x1 x2 ↔
    natinf_max x1 x2 = x1.
  Proof.
    setoid_rewrite natinf_le_iff_max. rewrite (comm natinf_max) //.
  Qed.
  Lemma natinf_max_l x1 x2 :
    natinf_le x2 x1 →
    natinf_max x1 x2 = x1.
  Proof.
    rewrite natinf_le_iff_max (comm natinf_max) //.
  Qed.
  Lemma natinf_max_r x1 x2 :
    natinf_le x1 x2 →
    natinf_max x1 x2 = x2.
  Proof.
    rewrite (comm natinf_max). apply natinf_max_l.
  Qed.
End natinf_max.

Section natinf_le.
  Lemma natinf_le_inf x :
    natinf_le x natinf_inf.
  Proof.
    apply right_id, _.
  Qed.

  Lemma natinf_le_min_1 x y :
    natinf_le (natinf_min x y) x.
  Proof.
    rewrite /natinf_le {1}(comm natinf_min x y) -assoc idemp (comm natinf_min) //.
  Qed.
  Lemma natinf_le_min_2 x y :
    natinf_le (natinf_min y x) x.
  Proof.
    rewrite comm. apply natinf_le_min_1.
  Qed.

  Lemma natinf_le_max_1 x y :
    natinf_le x (natinf_max x y).
  Proof.
    destruct (natinf_min_max_case x y) as [(? & ->) | (? & ->)]; first done.
    rewrite /natinf_le idemp //.
  Qed.
  Lemma natinf_le_max_2 x y :
    natinf_le x (natinf_max y x).
  Proof.
    rewrite comm. apply natinf_le_max_1.
  Qed.

  #[global] Instance natinf_le_proper :
    Proper ((≤) ==> natinf_le) natinf_nat.
  Proof.
    intros n1 n2 Hle. rewrite /natinf_le /=. f_equal. lia.
  Qed.
  #[global] Instance natinf_le_inj :
    Inj (≤) natinf_le natinf_nat.
  Proof.
    intros n1 n2. rewrite /natinf_le /=. intros <-%(inj natinf_nat). lia.
  Qed.
  Lemma natinf_le_le n1 n2 :
    n1 ≤ n2 ↔
    natinf_le (natinf_nat n1) (natinf_nat n2).
  Proof.
    split; [solve_proper | apply inj, _].
  Qed.

  #[global] Instance natinf_le_refl :
    Reflexive natinf_le.
  Proof.
    intros x. apply (idemp natinf_min).
  Qed.
  #[global] Instance natinf_le_trans :
    Transitive natinf_le.
  Proof.
    intros x1 x2 x3 <- <-. rewrite assoc. apply natinf_le_min_2.
  Qed.
  #[global] Instance natinf_le_antisymm :
    AntiSymm (=) natinf_le.
  Proof.
    intros x1 x2 Hle1 Hle2. rewrite -Hle1 -{2}Hle2 (comm natinf_min) //.
  Qed.
  #[global] Instance natinf_le_total :
    Total natinf_le.
  Proof.
    intros x1 x2. rewrite /natinf_le (comm natinf_min x2 x1). apply natinf_min_case.
  Qed.
End natinf_le.

Section natinf_ge.
  Lemma natinf_ge_inf x :
    natinf_ge natinf_inf x.
  Proof.
    apply natinf_le_inf.
  Qed.

  Lemma natinf_ge_min_1 x y :
    natinf_ge x (natinf_min x y).
  Proof.
    apply natinf_le_min_1.
  Qed.
  Lemma natinf_ge_min_2 x y :
    natinf_ge x (natinf_min y x).
  Proof.
    apply natinf_le_min_2.
  Qed.

  Lemma natinf_ge_max_1 x y :
    natinf_ge (natinf_max x y) x.
  Proof.
    apply natinf_le_max_1.
  Qed.
  Lemma natinf_ge_max_2 x y :
    natinf_ge (natinf_max y x) x.
  Proof.
    apply natinf_le_max_2.
  Qed.

  #[global] Instance natinf_ge_proper :
    Proper (ge ==> natinf_ge) natinf_nat.
  Proof.
    rewrite /natinf_ge. solve_proper.
  Qed.
  #[global] Instance natinf_ge_inj :
    Inj ge natinf_ge natinf_nat.
  Proof.
    intros x1 x2. apply natinf_le_inj.
  Qed.
  Lemma natinf_ge_ge n1 n2 :
    n1 ≥ n2 ↔
    natinf_ge (natinf_nat n1) (natinf_nat n2).
  Proof.
    apply natinf_le_le.
  Qed.

  #[global] Instance natinf_ge_refl :
    Reflexive natinf_ge.
  Proof.
    apply natinf_le_refl.
  Qed.
  #[global] Instance natinf_ge_trans :
    Transitive natinf_ge.
  Proof.
    rewrite /Transitive. intros. eapply natinf_le_trans; done.
  Qed.
  #[global] Instance natinf_ge_antisymm :
    AntiSymm (=) natinf_ge.
  Proof.
    rewrite /AntiSymm. eauto using natinf_le_antisymm.
  Qed.
  #[global] Instance natinf_ge_total :
    Total natinf_ge.
  Proof.
    rewrite /Total. eauto using natinf_le_total.
  Qed.
End natinf_ge.
