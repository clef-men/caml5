From stdpp Require Export
  list.

From caml5 Require Import
  prelude.

Section filter.
  Context `(P : A → Prop) `{∀ x, Decision (P x)}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.
  #[local] Arguments filter {_ _ _} _ {_} !_ /.

  Lemma filter_eq_cons l x k :
    filter P l = x :: k →
    P x.
  Proof.
    intros ?%(f_equal head)%head_Some_elem_of%elem_of_list_filter. naive_solver.
  Qed.
End filter.
