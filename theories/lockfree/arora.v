From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  record_three
  array.
From caml5.lockfree Require Export
  base.

Definition arora_namespace :=
  lockfree_namespace .@ "arora".

Class AroraGS Σ `{!heapGS Σ} := {
}.

Definition arora_Σ := #[
].
Lemma subG_arora_Σ Σ `{!heapGS Σ} :
  subG arora_Σ Σ →
  AroraGS Σ.
Proof.
  solve_inG.
Qed.

Section arora_GS.
  Context `{!heapGS Σ} `{!AroraGS Σ}.

  Notation arora_offset_front := 0%Z.
  Notation arora_offset_back := 1%Z.
  Notation arora_offset_array := 2%Z.

  Notation "t '.(front)'" := (t +ₗ arora_offset_front)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(back)'" := (t +ₗ arora_offset_back)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(array)'" := (t +ₗ arora_offset_array)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(front)'" := (t +ₗ #arora_offset_front)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(back)'" := (t +ₗ #arora_offset_back)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(array)'" := (t +ₗ #arora_offset_array)%E
  ( at level 5
  ) : expr_scope.

  Definition arora_make : val :=
    λ: "sz",
      record_three_make #0 #0 (circular_array_make "sz").

  Definition arora_push : val :=
    λ: "t" "v",
      let: "back" := !"t".(back) in
      circular_array_set !"t".(array) "back" "v" ;;
      "t".(back) <- "back" + #1.

  Definition arora_steal : val :=
    rec: "arora_steal" "t" :=
      let: "front" := !"t".(front) in
      let: "back" := !"t".(back) in
      if: "front" < "back" then (
        let: "v" := circular_array_get !"t".(array) "front" in
        if: CAS "t".(front) "front" ("front" + #1) then (
          SOME "v"
        ) else (
          "arora_steal" "t"
        )
      ) else (
        NONE
      ).

  Definition arora_pop : val :=
    λ: "t",
      let: "back" := !"t".(back) - #1 in
      let: "arr" := !"t".(array) in
      "t".(back) <- "back" ;;
      let: "front" := !"t".(front) in
      if: "back" < "front" then (
        "t".(back) <- "front" ;;
        NONE
      ) else (
        let: "v" := circular_array_get "arr" "back" in
        if: "front" < "back" then (
          SOME "v"
        ) else (
          if: CAS "t".(front) "front" ("front" + #1) then (
            "t".(back) <- "front" + #1 ;;
            SOME "v"
          ) else (
            "t".(back) <- "front" + #1 ;;
            NONE
          )
        )
      ).
End arora_GS.
