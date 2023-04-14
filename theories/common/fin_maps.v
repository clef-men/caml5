From stdpp Require Export
  fin_maps.

From caml5 Require Import
  prelude.

Section insert.
  Context `{FinMap K M}.

  Lemma insert_inj {X} k x1 (m1 : M X) x2 m2 :
    m1 !! k = None →
    m2 !! k = None →
    <[k := x1]> m1 = <[k := x2]> m2 →
    x1 = x2 ∧ m1 = m2.
  Proof.
    intros Hlookup1 Hlookup2 Heq.
    assert (x1 = x2) as <-.
    { apply (inj Some).
      rewrite -(lookup_insert m1 k x1) -(lookup_insert m2 k x2) Heq //.
    }
    split; first done. rewrite !insert_union_singleton_l in Heq.
    eapply map_union_cancel_l; eauto using map_disjoint_singleton_r_2.
  Qed.
End insert.

Section map_seq.
  Context `{FinMap nat M} {X : Type}.
  Implicit Types x : X.
  Implicit Types xs : list X.

  #[global] Instance map_seq_inj start :
    Inj (=) (=) (map_seq (M := M X) start).
  Proof.
    rewrite /Inj.
    intros xs1. revert start. induction xs1 as [| x xs1 IH]; intros start xs2 Heq.
    - destruct xs2; [done | eelim insert_non_empty; done].
    - destruct xs2; first (eelim insert_non_empty; done).
      eelim insert_inj; [| apply map_seq_cons_disjoint.. | done].
      intros <- Heq'. f_equal. eapply IH. done.
  Qed.
End map_seq.
