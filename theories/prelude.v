From Coq.ssr Require Export
  ssreflect.

From stdpp Require Export
  prelude.

#[export] Set Default Proof Using "Type*".
#[export] Set Suggest Proof Using.

Ltac done :=
  stdpp.tactics.done.
