From stdpp Require Export
  namespaces
  strings.

From iris.base_logic Require Export
  lib.invariants.

From caml5 Require Import
  prelude.
From caml5.program_logic Require Export
  atomic.
From caml5.lang Require Export
  lang.

Definition caml5_namespace :=
  nroot .@ "caml5".
