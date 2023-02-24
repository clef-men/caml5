From iris.heap_lang Require Export
  notation.

From caml5 Require Import
  prelude.

Notation Fail := (App #() #())
( only parsing
).

Notation "e .0" := (e +ₗ #0%Z)%E
( at level 2,
  left associativity,
  format "e .0"
) : expr_scope.
Notation "e .1" := (e +ₗ #1%Z)%E
( at level 2,
  left associativity,
  format "e .1"
) : expr_scope.
Notation "e .2" := (e +ₗ #2%Z)%E
( at level 2,
  left associativity,
  format "e .2"
) : expr_scope.
Notation "e .3" := (e +ₗ #3%Z)%E
( at level 2,
  left associativity,
  format "e .3"
) : expr_scope.
