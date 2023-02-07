From iris.heap_lang Require Export
  notation.

From caml5 Require Import
  prelude.

Notation Fail := (App #() #())
( only parsing
).
