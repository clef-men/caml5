From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Import
  record3
  array.
From caml5.concurrent Require Import
  domain
  ws_deques_ext1
  condition.

Section ws_deques_ext1.
  Context `{!heapGS Σ} `{counter_G : !CounterG Σ}.
  Context `(ws_deques : ws_deques_ext1 Σ ws_deques_unboxed).
  Context {mutex_unboxed} {mutex : mutex Σ mutex_unboxed}.
  Context {condition_unboxed} (condition : condition Σ mutex condition_unboxed).

  Notation "t '.(domains)'" := t.1%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(ws_deques)'" := t.2%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(domains)'" := t.1%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(ws_deques)'" := t.2%E
  ( at level 5
  ) : expr_scope.

  Notation "hdl '.(handle_ws_deques)'" := hdl.1
  ( at level 5
  ) : stdpp_scope.
  Notation "hdl '.(handle_id)'" := hdl.2
  ( at level 5
  ) : stdpp_scope.
  Notation "hdl '.(handle_ws_deques)'" := hdl.1%E
  ( at level 5
  ) : expr_scope.
  Notation "hdl '.(handle_id)'" := hdl.2%E
  ( at level 5
  ) : expr_scope.

  Notation "fut '.(future_mutex)'" := fut.(0)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "fut '.(future_condition)'" := fut.(1)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "fut '.(future_result)'" := fut.(2)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "fut '.(future_mutex)'" := fut.(0)%E
  ( at level 5
  ) : expr_scope.
  Notation "fut '.(future_condition)'" := fut.(1)%E
  ( at level 5
  ) : expr_scope.
  Notation "fut '.(future_result)'" := fut.(2)%E
  ( at level 5
  ) : expr_scope.

  #[local] Definition domain_pool_worker_aux : val :=
    rec: "domain_pool_worker_aux" "hdl" :=
      match: ws_deques.(ws_deques_ext1_try_steal_once) "hdl".(handle_ws_deques) "hdl".(handle_id) with
        NONE =>
          "domain_pool_worker_aux" "hdl"
      | SOME "task" =>
          "task"
      end.
  #[local] Definition domain_pool_worker : val :=
    rec: "domain_pool_worker" "hdl" :=
      let: "task" :=
        match: ws_deques.(ws_deques_ext1_pop) "hdl".(handle_ws_deques) "hdl".(handle_id) with
          NONE =>
            domain_pool_worker_aux "hdl"
        | SOME "task" =>
            "task"
        end
      in
      match: "task" with
        NONE =>
          #()
      | SOME "task" =>
          "task" "hdl" ;;
          "domain_pool_worker" "hdl"
      end.

  Definition domain_pool_make : val :=
    λ: "sz",
      let: "ws_deques" := ws_deques.(ws_deques_ext1_make) "sz" in
      let: "cntr" := counter_make #() in
      counter_incr "cntr" ;;
      let: "doms" :=
        array_init ("sz" - #1) (λ: <>,
          let: "id" := counter_incr "cntr" in
          domain_spawn (λ: <>, domain_pool_worker ("ws_deques", "id"))
        )
      in
      ("ws_deques", "doms").

  Definition domain_pool_size : val :=
    λ: "t",
      array_size "t".(domains).

  Definition domain_pool_async : val :=
    λ: "hdl" "task",
      let: "mtx" := mutex.(mutex_make) #() in
      let: "cond" := condition.(condition_make) "mtx" in
      let: "fut" := record3_make "mutx" "cond" NONE in
      let: "task" := λ: "hdl",
        let: "res" := "task" "hdl" in
        mutex.(mutex_protect) "mtx" (λ: <>,
          "fut".(future_result) <- SOME "res"
        ) ;;
        condition.(condition_signal) "cond"
      in
      ws_deques.(ws_deques_ext1_push) "hdl".(handle_ws_deques) "hdl".(handle_id) (SOME "task") ;;
      "fut".

  Definition domain_pool_await : val :=
    λ: "fut",
      let: "mtx" := !"fut".(future_mutex) in
      let: "cond" := !"fut".(future_condition) in
      mutex.(mutex_protect) "mtx" (λ: <>,
        condition.(condition_wait_while) "cond" "mtx" (λ: <>,
          !"fut".(future_result) = NONE
        )
      ) ;;
      match: !"fut".(future_result) with
        NONE => Fail
      | SOME "res" => "res"
      end.

  Definition domain_pool_run : val :=
    λ: "t" "task",
      "task" ("t".(ws_deques), #0).

  #[local] Definition domain_pool_kill_aux : val :=
    rec: "domain_pool_kill_aux" "ws_deques" "i" :=
      if: "i" = #1 then #() else (
        ws_deques.(ws_deques_ext1_push) "ws_deques" #0 NONE ;;
        "domain_pool_kill_aux" "t" ("i" - #1)
      ).
  Definition domain_pool_kill : val :=
    λ: "t",
      domain_pool_kill_aux "t".(ws_deques) (domain_pool_size "t") ;;
      array_iter "t".(domains) domain_join.
End ws_deques_ext1.

#[global] Opaque domain_pool_make.
#[global] Opaque domain_pool_size.
#[global] Opaque domain_pool_async.
#[global] Opaque domain_pool_await.
#[global] Opaque domain_pool_run.
#[global] Opaque domain_pool_kill.

Module fibonacci.
  Context `{!heapGS Σ} `{counter_G : !CounterG Σ}.
  Context `(ws_deques : ws_deques_ext1 Σ ws_deques_unboxed).
  Context {mutex_unboxed} {mutex : mutex Σ mutex_unboxed}.
  Context {condition_unboxed} (condition : condition Σ mutex condition_unboxed).

  Definition fibonacci_aux : val :=
    rec: "fibonacci_aux" "n" "hdl" :=
      if: "n" ≤ #1 then (
        "n"
      ) else (
        let: "fut1" := (domain_pool_async ws_deques condition) "hdl" ("fibonacci_aux" ("n" - #1)) in
        let: "fut2" := (domain_pool_async ws_deques condition) "hdl" ("fibonacci_aux" ("n" - #2)) in
        let: "res1" := (domain_pool_await condition) "fut1" in
        let: "res1" := (domain_pool_await condition) "fut2" in
        "res1" + "res2"
      ).
  Definition fibonacci : val :=
    λ: "pool" "n",
      domain_pool_run "pool" (fibonacci_aux "n").
End fibonacci.
