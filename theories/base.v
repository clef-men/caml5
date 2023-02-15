From stdpp Require Export
  namespaces
  strings.

From iris.bi Require Export
  lib.fractional.
From iris.base_logic Require Export
  lib.invariants.

From caml5 Require Import
  prelude.

Definition caml5_namespace :=
  nroot .@ "caml5".
