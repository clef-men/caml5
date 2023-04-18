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
    pose proof (elem_of_list_here x k) as Hx.
    intros Hl. rewrite -Hl elem_of_list_filter in Hx. naive_solver.
  Qed.
End filter.
