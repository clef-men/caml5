From caml5 Require Export
  base.
From caml5.program_logic Require Export
  atomic.
From caml5.lang Require Export
  lang.

Definition std_namespace :=
  caml5_namespace .@ "std".
