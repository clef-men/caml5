From Coq.Logic Require Import
  FunctionalExtensionality.

From iris.algebra Require Import
  list.

From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.base_logic Require Import
  lib.excl
  lib.auth_excl
  lib.auth_nat_max
  lib.mono_list.
From caml5.lang Require Import
  wise_prophet
  identifier
  notations
  proofmode.
From caml5.std Require Import
  inf_array.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  ws_deque.

#[local] Program Definition inf_chaselev_deque_prophet := {|
  typed_prophet_type :=
    nat * bool * nat * identifier ;
  typed_prophet_of_val w v :=
    match w with
    | (LitV (LitInt front), LitV (LitBool b))%V =>
        match v with
        | (LitV (LitInt front'), LitV (LitProphecy id))%V =>
            Some (Z.to_nat front, b, Z.to_nat front', id)
        | _ =>
            None
        end
    | _ =>
        None
    end ;
  typed_prophet_to_val '(front, b, front', id) :=
    ((#front, #b)%V, (#front', #id)%V) ;
|}.
Solve Obligations of inf_chaselev_deque_prophet with
  try done.
Next Obligation.
  intros (((front & b) & front') & id) w v ?. simplify. rewrite !Nat2Z.id //.
Qed.

Class InfChaselevDequeG Σ `{!heapGS Σ} (array : inf_array Σ false) := {
  inf_chaselev_deque_G_ctl_G : AuthExclG Σ (ZO * (nat -d> valO)) ;
  inf_chaselev_deque_G_front_G : AuthNatMaxG Σ ;
  inf_chaselev_deque_G_hist_G : MonoListG Σ val ;
  inf_chaselev_deque_G_pub_G : AuthExclG Σ (listO valO) ;
  inf_chaselev_deque_G_lock_G : ExclG Σ unitO ;
  inf_chaselev_deque_G_prophet_G : WiseProphetG Σ inf_chaselev_deque_prophet ;
  inf_chaselev_deque_G_winner_G : AuthExclG Σ (natO * (valO -d> ▶ ∙)) ;
}.
#[local] Existing Instance inf_chaselev_deque_G_ctl_G.
#[local] Existing Instance inf_chaselev_deque_G_front_G.
#[local] Existing Instance inf_chaselev_deque_G_hist_G.
#[local] Existing Instance inf_chaselev_deque_G_pub_G.
#[local] Existing Instance inf_chaselev_deque_G_lock_G.
#[local] Existing Instance inf_chaselev_deque_G_prophet_G.
#[local] Existing Instance inf_chaselev_deque_G_winner_G.

Definition inf_chaselev_deque_Σ := #[
  auth_excl_Σ (ZO * (nat -d> valO)) ;
  auth_nat_max_Σ ;
  mono_list_Σ val ;
  auth_excl_Σ (listO valO) ;
  excl_Σ unitO ;
  wise_prophet_Σ inf_chaselev_deque_prophet ;
  auth_excl_Σ (natO * (valO -d> ▶ ∙))
].
Lemma subG_inf_chaselev_deque_Σ Σ `{!heapGS Σ} array :
  subG inf_chaselev_deque_Σ Σ →
  InfChaselevDequeG Σ array.
Proof.
  pose subG_wise_prophet_Σ.
  solve_inG.
Qed.

Module base.
Section inf_chaselev_deque_G.
  Context `{!heapGS Σ} {array} `{inf_chaselev_deque_G : !InfChaselevDequeG Σ array}.
  Implicit Types front : nat.
  Implicit Types back : Z.
  Implicit Types l : loc.
  Implicit Types p : proph_id.
  Implicit Types id : identifier.
  Implicit Types v t data : val.
  Implicit Types hist pub : list val.
  Implicit Types priv : nat → val.
  Implicit Types prophs : list inf_chaselev_deque_prophet.(typed_prophet_type).
  Implicit Types Φ : val → iProp Σ.

  Notation "t '.(front)'" := t.(0)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(back)'" := t.(1)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(data)'" := t.(2)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(prophecy)'" := t.(3)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(front)'" := t.(0)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(back)'" := t.(1)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(data)'" := t.(2)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(prophecy)'" := t.(3)%E
  ( at level 5
  ) : expr_scope.

  Definition inf_chaselev_deque_make : val :=
    λ: <>,
      let: "t" := AllocN #4 #0 in
      "t".(data) <- array.(inf_array_make) #() ;;
      "t".(prophecy) <- NewProph ;;
      "t".

  Definition inf_chaselev_deque_push : val :=
    λ: "t" "v",
      let: "back" := !"t".(back) in
      array.(inf_array_set) !"t".(data) "back" "v" ;;
      "t".(back) <- "back" + #1.

  Definition inf_chaselev_deque_steal : val :=
    rec: "inf_chaselev_deque_steal" "t" :=
      let: "id" := NewId in
      let: "front" := !"t".(front) in
      let: "back" := !"t".(back) in
      if: "front" < "back" then (
        let: "v" := array.(inf_array_get) !"t".(data) "front" in
        if: Snd $ Resolve (CmpXchg "t".(front) "front" ("front" + #1)) !"t".(prophecy) ("front", "id") then (
          SOME "v"
        ) else (
          "inf_chaselev_deque_steal" "t"
        )
      ) else (
        NONE
      ).

  Definition inf_chaselev_deque_pop : val :=
    λ: "t",
      let: "id" := NewId in
      let: "back" := !"t".(back) - #1 in
      "t".(back) <- "back" ;;
      let: "front" := !"t".(front) in
      if: "back" < "front" then (
        "t".(back) <- "front" ;;
        NONE
      ) else (
        if: "front" < "back" then (
          SOME (array.(inf_array_get) !"t".(data) "back")
        ) else (
          if: Snd $ Resolve (CmpXchg "t".(front) "front" ("front" + #1)) !"t".(prophecy) ("front", "id") then (
            "t".(back) <- "front" + #1 ;;
            SOME (array.(inf_array_get) !"t".(data) "back")
          ) else (
            "t".(back) <- "front" + #1 ;;
            NONE
          )
        )
      ).

  Notation inf_chaselev_deque_meta_ctl :=
    (nroot .@ "ctl").
  Notation inf_chaselev_deque_meta_front :=
    (nroot .@ "front").
  Notation inf_chaselev_deque_meta_hist :=
    (nroot .@ "hist").
  Notation inf_chaselev_deque_meta_pub :=
    (nroot .@ "pub").
  Notation inf_chaselev_deque_meta_lock :=
    (nroot .@ "lock").
  Notation inf_chaselev_deque_meta_prophet :=
    (nroot .@ "prophet").
  Notation inf_chaselev_deque_meta_winner :=
    (nroot .@ "winner").

  #[local] Definition inf_chaselev_deque_ctl₁ γ_ctl back priv :=
    auth_excl_auth (auth_excl_G := inf_chaselev_deque_G_ctl_G) γ_ctl (DfracOwn 1) (back, priv).
  #[local] Definition inf_chaselev_deque_ctl₂ γ_ctl back priv :=
    auth_excl_frag (auth_excl_G := inf_chaselev_deque_G_ctl_G) γ_ctl (back, priv).

  #[local] Definition inf_chaselev_deque_front_auth γ_front front :=
    auth_nat_max_auth γ_front (DfracOwn 1) front.
  #[local] Definition inf_chaselev_deque_front_frag γ_front front :=
    auth_nat_max_frag γ_front front.

  #[local] Definition inf_chaselev_deque_hist_auth γ_hist hist :=
    mono_list_auth γ_hist 1 hist.
  #[local] Definition inf_chaselev_deque_hist_frag γ_hist i v :=
    mono_list_mapsto γ_hist i v.

  #[local] Definition inf_chaselev_deque_pub₁ γ_pub pub :=
    auth_excl_frag (auth_excl_G := inf_chaselev_deque_G_pub_G) γ_pub pub.
  #[local] Definition inf_chaselev_deque_pub₂ γ_pub pub :=
    auth_excl_auth (auth_excl_G := inf_chaselev_deque_G_pub_G) γ_pub (DfracOwn 1) pub.

  #[local] Definition inf_chaselev_deque_lock γ_lock :=
    excl γ_lock ().

  #[local] Definition inf_chaselev_deque_winner₁ γ_winner front Φ :=
    auth_excl_frag (auth_excl_G := inf_chaselev_deque_G_winner_G) γ_winner (front, Next ∘ Φ).
  #[local] Definition inf_chaselev_deque_winner₂ γ_winner front Φ :=
    auth_excl_auth (auth_excl_G := inf_chaselev_deque_G_winner_G) γ_winner (DfracOwn 1) (front, Next ∘ Φ).
  #[local] Definition inf_chaselev_deque_winner γ_winner : iProp Σ :=
    ∃ front Φ1 Φ2,
    inf_chaselev_deque_winner₁ γ_winner front Φ1 ∗
    inf_chaselev_deque_winner₂ γ_winner front Φ2.

  Definition inf_chaselev_deque_model t pub : iProp Σ :=
    ∃ l γ_pub,
    ⌜t = #l⌝ ∗
    (* metas *)
    meta l inf_chaselev_deque_meta_pub γ_pub ∗
    (* public values *)
    inf_chaselev_deque_pub₂ γ_pub pub.

  Definition inf_chaselev_deque_owner t : iProp Σ :=
    ∃ l γ_ctl γ_lock back priv,
    ⌜t = #l⌝ ∗
    (* metas *)
    meta l inf_chaselev_deque_meta_ctl γ_ctl ∗
    meta l inf_chaselev_deque_meta_lock γ_lock ∗
    (* control token *)
    inf_chaselev_deque_ctl₂ γ_ctl back priv ∗
    (* lock *)
    inf_chaselev_deque_lock γ_lock.

  #[local] Definition inf_chaselev_deque_atomic_update γ_pub ι Φ : iProp Σ :=
    AU << ∃∃ pub,
      inf_chaselev_deque_pub₂ γ_pub pub
    >>
      @ ⊤ ∖ ↑ι, ∅
    << ∀∀ v pub',
      ⌜pub = v :: pub'⌝ ∗ inf_chaselev_deque_pub₂ γ_pub pub',
      COMM Φ (SOMEV v)
    >>.
  #[local] Definition inf_chaselev_deque_state_inner₁ γ_winner :=
    inf_chaselev_deque_winner γ_winner.
  #[local] Definition inf_chaselev_deque_state₁ γ_hist γ_winner front back hist : iProp Σ :=
    (* physical configuration *)
    ⌜Z.of_nat front = back⌝ ∗
    (* history values *)
    inf_chaselev_deque_hist_auth γ_hist hist ∗
    ⌜length hist = front⌝ ∗
    (* inner state *)
    inf_chaselev_deque_state_inner₁ γ_winner.
  #[local] Definition inf_chaselev_deque_state_inner₂ γ_pub γ_winner ι front prophs : iProp Σ :=
    match filter (λ '(_, _, front', _), front' = front) prophs with
    | [] =>
        inf_chaselev_deque_winner γ_winner
    | (_, _, _, id) :: _ =>
          inf_chaselev_deque_winner γ_winner
        ∨ identifier_model id ∗
          ∃ Φ,
          inf_chaselev_deque_winner₁ γ_winner front Φ ∗
          inf_chaselev_deque_atomic_update γ_pub ι Φ
    end.
  #[local] Definition inf_chaselev_deque_state₂ γ_hist γ_pub γ_winner ι front back hist pub prophs : iProp Σ :=
    (* physical configuration *)
    ⌜(front < back)%Z⌝ ∗
    (* history values *)
    inf_chaselev_deque_hist_auth γ_hist (hist ++ [pub !!! 0]) ∗
    ⌜length hist = front⌝ ∗
    (* inner state *)
    inf_chaselev_deque_state_inner₂ γ_pub γ_winner ι front prophs.
  #[local] Definition inf_chaselev_deque_state_inner₃₁ γ_winner front hist prophs : iProp Σ :=
    match filter (λ '(_, _, front', _), front' = front) prophs with
    | [] =>
        inf_chaselev_deque_winner γ_winner
    | (_, _, _, id) :: _ =>
          inf_chaselev_deque_winner γ_winner
        ∨ identifier_model id ∗
          ∃ Φ,
          inf_chaselev_deque_winner₁ γ_winner front Φ ∗
          Φ (SOMEV (hist !!! front))
    end.
  #[local] Definition inf_chaselev_deque_state₃₁ γ_hist γ_winner front back hist prophs : iProp Σ :=
    (* physical configuration *)
    ⌜Z.of_nat front = back⌝ ∗
    (* history values *)
    inf_chaselev_deque_hist_auth γ_hist hist ∗
    ⌜length hist = S front⌝ ∗
    (* inner state *)
    inf_chaselev_deque_state_inner₃₁ γ_winner front hist prophs.
  #[local] Definition inf_chaselev_deque_state_inner₃₂ γ_winner :=
    inf_chaselev_deque_winner γ_winner.
  #[local] Definition inf_chaselev_deque_state₃₂ γ_hist γ_winner front back hist : iProp Σ :=
    (* physical configuration *)
    ⌜Z.of_nat front = (back + 1)%Z⌝ ∗
    (* history values *)
    inf_chaselev_deque_hist_auth γ_hist hist ∗
    ⌜length hist = front⌝ ∗
    (* inner state *)
    inf_chaselev_deque_state_inner₃₂ γ_winner.
  #[local] Definition inf_chaselev_deque_state₃ γ_hist γ_lock γ_winner front back hist pub prophs : iProp Σ :=
    inf_chaselev_deque_lock γ_lock ∗
    ( inf_chaselev_deque_state₃₁ γ_hist γ_winner front back hist prophs
    ∨ inf_chaselev_deque_state₃₂ γ_hist γ_winner front back hist
    ).
  #[local] Definition inf_chaselev_deque_state γ_hist γ_pub γ_lock γ_winner ι front back hist pub prophs : iProp Σ :=
      inf_chaselev_deque_state₁ γ_hist γ_winner front back hist
    ∨ inf_chaselev_deque_state₂ γ_hist γ_pub γ_winner ι front back hist pub prophs
    ∨ inf_chaselev_deque_state₃ γ_hist γ_lock γ_winner front back hist pub prophs.

  #[local] Definition inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p : iProp Σ :=
    ∃ front back hist pub priv past prophs,
    (* mutable physical fields *)
    l.(front) ↦ #front ∗ l.(back) ↦ #back ∗
    (* control token *)
    inf_chaselev_deque_ctl₁ γ_ctl back priv ∗
    (* front authority *)
    inf_chaselev_deque_front_auth γ_front front ∗
    (* data model *)
    array.(inf_array_model') data (hist ++ pub) priv ∗
    (* public values *)
    inf_chaselev_deque_pub₁ γ_pub pub ∗
    ⌜length pub = Z.to_nat (back - front)⌝ ∗
    (* prophet model *)
    wise_prophet_model inf_chaselev_deque_prophet p γ_prophet past prophs ∗
    ⌜Forall (λ '(_, _, front', _), front' < front) past⌝ ∗
    (* state *)
    inf_chaselev_deque_state γ_hist γ_pub γ_lock γ_winner ι front back hist pub prophs.
  Definition inf_chaselev_deque_inv t ι : iProp Σ :=
    ∃ l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner data p,
    ⌜t = #l⌝ ∗
    (* metas *)
    meta l inf_chaselev_deque_meta_ctl γ_ctl ∗
    meta l inf_chaselev_deque_meta_front γ_front ∗
    meta l inf_chaselev_deque_meta_hist γ_hist ∗
    meta l inf_chaselev_deque_meta_pub γ_pub ∗
    meta l inf_chaselev_deque_meta_lock γ_lock ∗
    meta l inf_chaselev_deque_meta_prophet γ_prophet ∗
    meta l inf_chaselev_deque_meta_winner γ_winner ∗
    (* immutable physical fields *)
    l.(data) ↦□ data ∗
    l.(prophecy) ↦□ #p ∗
    (* main invariant *)
    inv ι (inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p).

  #[global] Instance inf_chaselev_deque_model_timeless t pub :
    Timeless (inf_chaselev_deque_model t pub).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_chaselev_deque_owner_timeless t :
    Timeless (inf_chaselev_deque_owner t).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_chaselev_deque_inv_persistent t ι :
    Persistent (inf_chaselev_deque_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma inf_chaselev_deque_ctl_alloc :
    ⊢ |==> ∃ γ_ctl,
      inf_chaselev_deque_ctl₁ γ_ctl 0 (λ _, #()) ∗
      inf_chaselev_deque_ctl₂ γ_ctl 0 (λ _, #()).
  Proof.
    iMod (auth_excl_alloc' (auth_excl_G := inf_chaselev_deque_G_ctl_G) (0%Z, λ _, #())) as "(%γ_ctl & Hctl₁ & Hctl₂)".
    iExists γ_ctl. iFrame. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_ctl_agree γ_ctl back1 priv1 back2 priv2 :
    inf_chaselev_deque_ctl₁ γ_ctl back1 priv1 -∗
    inf_chaselev_deque_ctl₂ γ_ctl back2 priv2 -∗
    ⌜back1 = back2 ∧ priv1 = priv2⌝.
  Proof.
    iIntros "Hctl₁ Hctl₂".
    iDestruct (auth_excl_agree with "Hctl₁ Hctl₂") as %(? & ?%functional_extensionality).
    done.
  Qed.
  #[local] Lemma inf_chaselev_deque_ctl_update {γ_ctl back1 priv1 back2 priv2} back priv :
    inf_chaselev_deque_ctl₁ γ_ctl back1 priv1 -∗
    inf_chaselev_deque_ctl₂ γ_ctl back2 priv2 ==∗
      inf_chaselev_deque_ctl₁ γ_ctl back priv ∗
      inf_chaselev_deque_ctl₂ γ_ctl back priv.
  Proof.
    iIntros "Hctl₁ Hctl₂".
    iMod (auth_excl_update' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl2)".
    iFrame. done.
  Qed.

  #[local] Lemma inf_chaselev_deque_front_alloc :
    ⊢ |==> ∃ γ_front,
      inf_chaselev_deque_front_auth γ_front 0.
  Proof.
    iMod (auth_nat_max_alloc 0) as "(%γ_front & Hfront_auth)".
    iExists γ_front. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_front_valid γ_front front1 front2 :
    inf_chaselev_deque_front_auth γ_front front1 -∗
    inf_chaselev_deque_front_frag γ_front front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iApply auth_nat_max_valid.
  Qed.
  #[local] Lemma inf_chaselev_deque_front_auth_update {γ_front front} front' :
    front ≤ front' →
    inf_chaselev_deque_front_auth γ_front front ==∗
    inf_chaselev_deque_front_auth γ_front front'.
  Proof.
    intros. iApply auth_nat_max_update. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_front_frag_get γ_front front :
    inf_chaselev_deque_front_auth γ_front front -∗
    inf_chaselev_deque_front_frag γ_front front.
  Proof.
    iApply auth_nat_max_frag_get.
  Qed.

  #[local] Lemma inf_chaselev_deque_hist_alloc :
    ⊢ |==> ∃ γ_hist,
      inf_chaselev_deque_hist_auth γ_hist [].
  Proof.
    iMod (mono_list_alloc []) as "(%γ_hist & Hhist_auth & _)".
    iExists γ_hist. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_hist_frag_get {γ_hist hist} i v :
    hist !! i = Some v →
    inf_chaselev_deque_hist_auth γ_hist hist -∗
    inf_chaselev_deque_hist_frag γ_hist i v.
  Proof.
    iIntros "% Hhist_auth".
    iDestruct (mono_list_lb_get with "Hhist_auth") as "#Hhist_frag".
    iApply (mono_list_mapsto_get with "Hhist_frag"). done.
  Qed.
  #[local] Lemma inf_chaselev_deque_hist_agree γ_hist hist i v :
    inf_chaselev_deque_hist_auth γ_hist hist -∗
    inf_chaselev_deque_hist_frag γ_hist i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_auth_mapsto_lookup.
  Qed.
  #[local] Lemma inf_chaselev_deque_hist_update {γ_hist hist} v :
    inf_chaselev_deque_hist_auth γ_hist hist ==∗
    inf_chaselev_deque_hist_auth γ_hist (hist ++ [v]).
  Proof.
    iIntros "Hhist_auth".
    iMod (mono_list_auth_update_app [v] with "Hhist_auth") as "($ & _)". done.
  Qed.

  #[local] Lemma inf_chaselev_deque_pub_alloc :
    ⊢ |==> ∃ γ_pub,
      inf_chaselev_deque_pub₁ γ_pub [] ∗
      inf_chaselev_deque_pub₂ γ_pub [].
  Proof.
    iMod (auth_excl_alloc' (auth_excl_G := inf_chaselev_deque_G_pub_G) []) as "(%γ_pub & Hpub₁ & Hpub₂)".
    iExists γ_pub. iFrame. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_pub_agree γ_pub pub1 pub2 :
    inf_chaselev_deque_pub₁ γ_pub pub1 -∗
    inf_chaselev_deque_pub₂ γ_pub pub2 -∗
    ⌜pub1 = pub2⌝.
  Proof.
    iIntros "Hpub₁ Hpub₂".
    iDestruct (auth_excl_agree_L with "Hpub₂ Hpub₁") as %->. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_pub_update {γ_pub pub1 pub2} pub :
    inf_chaselev_deque_pub₁ γ_pub pub1 -∗
    inf_chaselev_deque_pub₂ γ_pub pub2 ==∗
      inf_chaselev_deque_pub₁ γ_pub pub ∗
      inf_chaselev_deque_pub₂ γ_pub pub.
  Proof.
    iIntros "Hpub₁ Hpub₂".
    iMod (auth_excl_update' with "Hpub₂ Hpub₁") as "(Hpub₂ & Hpub₁)".
    iFrame. done.
  Qed.

  #[local] Lemma inf_chaselev_deque_lock_alloc :
    ⊢ |==> ∃ γ_lock,
      inf_chaselev_deque_lock γ_lock.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma inf_chaselev_deque_lock_exclusive γ_lock :
    inf_chaselev_deque_lock γ_lock -∗
    inf_chaselev_deque_lock γ_lock -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.
  #[local] Lemma inf_chaselev_deque_lock_state γ_hist γ_pub γ_lock γ_winner ι front back hist pub prophs :
    inf_chaselev_deque_lock γ_lock -∗
    inf_chaselev_deque_state γ_hist γ_pub γ_lock γ_winner ι front back hist pub prophs -∗
      inf_chaselev_deque_lock γ_lock ∗
      ( inf_chaselev_deque_state₁ γ_hist γ_winner front back hist
      ∨ inf_chaselev_deque_state₂ γ_hist γ_pub γ_winner ι front back hist pub prophs
      ).
  Proof.
    iIntros "Hlock [Hstate | [Hstate | (Hlock' & Hstate)]]"; [iFrame.. |].
    iDestruct (inf_chaselev_deque_lock_exclusive with "Hlock Hlock'") as %[].
  Qed.

  #[local] Lemma inf_chaselev_deque_winner_alloc :
    ⊢ |==> ∃ γ_winner,
      inf_chaselev_deque_winner γ_winner.
  Proof.
  Admitted.
  #[local] Lemma inf_chaselev_deque_winner₂_exclusive γ_winner front Φ :
    inf_chaselev_deque_winner₂ γ_winner front Φ -∗
    inf_chaselev_deque_winner γ_winner -∗
    False.
  Proof.
  Admitted.
  #[local] Lemma inf_chaselev_deque_winner_agree {γ_winner front1 Φ1 front2 Φ2} v :
    inf_chaselev_deque_winner₁ γ_winner front1 Φ1 -∗
    inf_chaselev_deque_winner₂ γ_winner front2 Φ2 -∗
      ⌜front1 = front2⌝ ∗
      ▷ (Φ1 v ≡ Φ2 v) ∗
      inf_chaselev_deque_winner₁ γ_winner front1 Φ1 ∗
      inf_chaselev_deque_winner₂ γ_winner front1 Φ2.
  Proof.
  Admitted.
  #[local] Lemma inf_chaselev_deque_winner_update {γ_winner front1 Φ1 front2 Φ2} front Φ :
    inf_chaselev_deque_winner₁ γ_winner front1 Φ1 -∗
    inf_chaselev_deque_winner₂ γ_winner front2 Φ2 ==∗
      inf_chaselev_deque_winner₁ γ_winner front Φ ∗
      inf_chaselev_deque_winner₂ γ_winner front Φ.
  Proof.
  Admitted.
  #[local] Lemma inf_chaselev_deque_winner₂_state_inner₂ {γ_winner γ_pub ι front1 front2 prophs Φ} v :
    inf_chaselev_deque_winner₂ γ_winner front1 Φ -∗
    inf_chaselev_deque_state_inner₂ γ_pub γ_winner ι front2 prophs -∗
      ∃ id Φ',
      ⌜front1 = front2⌝ ∗
      ▷ (Φ' v ≡ Φ v) ∗
      inf_chaselev_deque_winner₁ γ_winner front1 Φ' ∗
      inf_chaselev_deque_winner₂ γ_winner front1 Φ ∗
      identifier_model id ∗
      inf_chaselev_deque_atomic_update γ_pub ι Φ'.
  Proof.
    iIntros "Hwinner₂ Hstate".
    rewrite /inf_chaselev_deque_state_inner₂. destruct (filter _ _) as [| (((? & ?) & ?) & id) prophs'] eqn:?.
    - iDestruct (inf_chaselev_deque_winner₂_exclusive with "Hwinner₂ Hstate") as %[].
    - iDestruct "Hstate" as "[Hwinner | (Hid & %Φ' & Hwinner₁ & HΦ')]".
      + iDestruct (inf_chaselev_deque_winner₂_exclusive with "Hwinner₂ Hwinner") as %[].
      + iDestruct (inf_chaselev_deque_winner_agree v with "Hwinner₁ Hwinner₂") as "(-> & Heq & Hwinner₁ & Hwinner₂)".
        iExists id, Φ'. iFrame. done.
  Qed.
  #[local] Lemma inf_chaselev_deque_winner₂_state_inner₃₁ {γ_winner front1 front2 hist prophs Φ} v :
    inf_chaselev_deque_winner₂ γ_winner front1 Φ -∗
    inf_chaselev_deque_state_inner₃₁ γ_winner front2 hist prophs -∗
      ∃ id Φ',
      ⌜front1 = front2⌝ ∗
      ▷ (Φ' v ≡ Φ v) ∗
      inf_chaselev_deque_winner₁ γ_winner front1 Φ' ∗
      inf_chaselev_deque_winner₂ γ_winner front1 Φ ∗
      identifier_model id ∗
      Φ' (SOMEV (hist !!! front1)).
  Proof.
    iIntros "Hwinner₂ Hstate".
    rewrite /inf_chaselev_deque_state_inner₃₁. destruct (filter _ _) as [| (((? & ?) & ?) & id) prophs'] eqn:?.
    - iDestruct (inf_chaselev_deque_winner₂_exclusive with "Hwinner₂ Hstate") as %[].
    - iDestruct "Hstate" as "[Hwinner | (Hid & %Φ' & Hwinner₁ & HΦ')]".
      + iDestruct (inf_chaselev_deque_winner₂_exclusive with "Hwinner₂ Hwinner") as %[].
      + iDestruct (inf_chaselev_deque_winner_agree v with "Hwinner₁ Hwinner₂") as "(-> & Heq & Hwinner₁ & Hwinner₂)".
        iExists id, Φ'. iFrame. done.
  Qed.

  Lemma inf_chaselev_deque_owner_exclusive t :
    inf_chaselev_deque_owner t -∗
    inf_chaselev_deque_owner t -∗
    False.
  Proof.
    iIntros "(%l & %γ_ctl & %γ_lock & %back & %priv & -> & #Hmeta_ctl & #Hmeta_lock & Hctl₂1 & Hlock1) (%_l & %_γ_ctl & %_γ_lock & %_back & %_priv & %Heq & #_Hmeta_ctl & #_Hmeta_lock & Hctl₂2 & Hlock2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_lock _Hmeta_lock") as %->.
    iApply (inf_chaselev_deque_lock_exclusive with "Hlock1 Hlock2").
  Qed.

  Lemma inf_chaselev_deque_make_spec ι :
    {{{ True }}}
      inf_chaselev_deque_make #()
    {{{ t,
      RET t;
      inf_chaselev_deque_inv t ι ∗
      inf_chaselev_deque_model t [] ∗
      inf_chaselev_deque_owner t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (Hl & (Hmeta & _))".
    iDestruct (array_cons with "Hl") as "(Hfront & Hl)".
    iDestruct (array_cons with "Hl") as "(Hback & Hl)".
    iDestruct (array_cons with "Hl") as "(Hdata & Hl)".
    iDestruct (array_cons with "Hl") as "(Hp & _)".
    rewrite loc_add_0 -{2}(loc_add_0 l) !loc_add_assoc /=.
    assert (1 + 1 = 2)%Z as -> by lia.
    assert (2 + 1 = 3)%Z as -> by lia.
    wp_pures.
    wp_apply (inf_array_make_spec with "[//]"). iIntros "%data Hdata_model".
    wp_pures. wp_store.
    wp_apply (wise_prophet_new_proph_spec with "[//]"). iIntros "%p %γ_prophet %prophs Hprophet_model".
    wp_pures. wp_store.
    iMod (mapsto_persist with "Hdata") as "#Hdata".
    iMod (mapsto_persist with "Hp") as "#Hp".
    iApply "HΦ".
    iMod inf_chaselev_deque_ctl_alloc as "(%γ_ctl & Hctl₁ & Hctl₂)".
    iMod inf_chaselev_deque_front_alloc as "(%γ_front & Hfront_auth)".
    iMod inf_chaselev_deque_hist_alloc as "(%γ_hist & Hhist_auth)".
    iMod inf_chaselev_deque_pub_alloc as "(%γ_pub & Hpub₁ & Hpub₂)".
    iMod inf_chaselev_deque_lock_alloc as "(%γ_lock & Hlock)".
    iMod inf_chaselev_deque_winner_alloc as "(%γ_winner & Hwinner)".
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_ctl) with "Hmeta") as "(Hmeta_ctl & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_front) with "Hmeta") as "(Hmeta_front & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_hist) with "Hmeta") as "(Hmeta_hist & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_pub) with "Hmeta") as "(Hmeta_pub & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_lock) with "Hmeta") as "(Hmeta_lock & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_prophet) with "Hmeta") as "(Hmeta_prophet & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_winner) with "Hmeta") as "(Hmeta_winner & _)"; first solve_ndisj.
    iMod (meta_set _ _ γ_ctl with "Hmeta_ctl") as "#Hmeta_ctl"; first done.
    iMod (meta_set _ _ γ_front with "Hmeta_front") as "#Hmeta_front"; first done.
    iMod (meta_set _ _ γ_hist with "Hmeta_hist") as "#Hmeta_hist"; first done.
    iMod (meta_set _ _ γ_pub with "Hmeta_pub") as "#Hmeta_pub"; first done.
    iMod (meta_set _ _ γ_lock with "Hmeta_lock") as "#Hmeta_lock"; first done.
    iMod (meta_set _ _ γ_prophet with "Hmeta_prophet") as "#Hmeta_prophet"; first done.
    iMod (meta_set _ _ γ_winner with "Hmeta_winner") as "#Hmeta_winner"; first done.
    iSplitR "Hctl₂ Hpub₂ Hlock".
    { repeat iExists _. iFrame "#∗". iSplitR; first done.
      iApply inv_alloc. iExists 0, 0%Z, [], [], (λ _, #()), [], prophs. iFrame.
      iSplit; first done.
      iSplit; first done.
      iLeft. iFrame. done.
    }
    iSplitL "Hpub₂".
    { iExists l, γ_pub. naive_solver. }
    iExists l, γ_ctl, γ_lock, 0%Z, (λ _, #()). iFrame "∗#". done.
  Qed.

  Lemma inf_chaselev_deque_push_spec t ι v :
    <<<
      inf_chaselev_deque_inv t ι ∗
      inf_chaselev_deque_owner t |
      ∀∀ pub, inf_chaselev_deque_model t pub
    >>>
      inf_chaselev_deque_push t v @ ↑ι
    <<<
      inf_chaselev_deque_model t (pub ++ [v]) |
      RET #(); inf_chaselev_deque_owner t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %γ_prophet & %γ_winner & %data & %p & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hmeta_prophet & #Hmeta_winner & #Hdata & #Hp & #Hinv) & (%l' & %_γ_ctl & %_γ_lock & %back & %priv & %Heq & #_Hmeta_ctl & #_Hmeta_lock & Hctl₂ & Hlock)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_ctl _Hmeta_ctl") as %<-. iClear "_Hmeta_ctl".
    iDestruct (meta_agree with "Hmeta_lock _Hmeta_lock") as %<-. iClear "_Hmeta_lock".

    wp_rec. wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
    (* do load back *)
    wp_load.
    (* we have lock, hence we are in state 1 or state 2, hence [0 ≤ back] *)
    iAssert ⌜0 ≤ back⌝%I%Z as %Hback.
    { iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as "(_ & [Hstate | Hstate])";
        iDestruct "Hstate" as "(%Hstate & _)"; iPureIntro; lia.
    }
    (* close invariant *)
    iModIntro. iSplitR "Hctl₂ Hlock HΦ".
    { repeat iExists _. iFrame. done. }
    clear- Hback.

    wp_pures.

    (* → [!#l.(data)] *)
    wp_load.

    (* → [array.(inf_array_set) data #back v] *)
    awp_apply (inf_array_set_spec' with "[//]") without "HΦ"; first done.
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & >Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
    iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
    { iFrame. repeat iExists _. iFrame. done. }
    (* update private values in control tokens *)
    set (priv' := <[0 := v]> priv).
    iMod (inf_chaselev_deque_ctl_update back priv' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
    (* we have lock, hence we are in state 1 or state 2 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as "(Hlock & Hstate)".
    (* hence [front ≤ back] and [length hist = front] *)
    iAssert (◇ ⌜front ≤ back ∧ length hist = front⌝%Z)%I as "#>%".
    { iDestruct "Hstate" as "[Hstate | Hstate]";
        iDestruct "Hstate" as "(>%Hstate & _ & >%Hhist & _)";
        iPureIntro; lia.
    }
    (* hence [back = length (hist ++ pub)] *)
    assert (Z.to_nat back = length (hist ++ pub)) as Heq. { rewrite app_length. lia. }
    rewrite Heq decide_False; last lia. rewrite Nat.sub_diag.
    (* close invariant *)
    iModIntro. iSplitR "Hctl₂ Hlock".
    { iExists front, back, hist, pub, priv', past, prophs. iFrame.
      iSplit; first auto.
      iSplit; first done.
      iDestruct "Hstate" as "[Hstate | Hstate]"; [iLeft | iRight; iLeft]; done.
    }
    iIntros "_ HΦ".
    clear.

    wp_pures.

    (* → [#l.(back) <- #(back + 1)] *)
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & %past & %prophs & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %(-> & ->).
    (* do increment back *)
    wp_store.
    (* update private values in control tokens *)
    set (priv'' i := priv (S i)).
    iMod (inf_chaselev_deque_ctl_update (back + 1) priv'' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
    (* begin transaction *)
    iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & _Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
    iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
    (* update public values *)
    set (pub' := pub ++ [v]).
    iMod (inf_chaselev_deque_pub_update pub' with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
    (* end transaction *)
    iMod ("HΦ" with "[Hpub₂]") as "HΦ".
    { repeat iExists _. iFrame "#∗". done. }
    (* update data model *)
    iDestruct (inf_array_model'_shift_l with "Hdata_model") as "Hdata_model"; first by intros [].
    rewrite -(assoc (++)) -/pub'.
    (* we have lock, hence we are in state 1 or state 2 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as "(Hlock & [Hstate | Hstate])".

    - iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hwinner)".
      destruct (nil_or_length_pos pub) as [-> |]; last lia.
      (* update history values *)
      iMod (inf_chaselev_deque_hist_update v with "Hhist_auth") as "Hhist_auth".
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock HΦ".
      { iExists front, (back + 1)%Z, hist, pub', priv'', past, prophs. iFrame.
        iSplit. { iPureIntro. simpl. lia. }
        iSplit; first done.
        iRight. iLeft. iFrame. iSplit; first auto with lia.
        rewrite /inf_chaselev_deque_state_inner₂. destruct (filter _ _) as [| (((_ & _) & _) & id) _]; auto.
      }
      clear.

      iApply "HΦ". repeat iExists _. iFrame "#∗". done.

    - iDestruct "Hstate" as "(%Hstate & Hhist_auth & %Hhist & Hwinner)".
      destruct pub as [| w pub]; first naive_solver lia.
      (* close invariant *)
      iModIntro. iSplitR "Hctl₂ Hlock HΦ".
      { iExists front, (back + 1)%Z, hist, pub', priv'', past, prophs. iFrame.
        iSplit. { iPureIntro. rewrite app_length. simpl in *. lia. }
        iSplit; first done.
        iRight. iLeft. iFrame. iPureIntro. lia.
      }
      clear.

      iApply "HΦ". repeat iExists _. iFrame "#∗". done.
  Qed.

  #[local] Lemma inf_chaselev_deque_get_weak l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p (i : nat) :
    {{{
      inv ι (inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p) ∗
      l.(data) ↦□ data
    }}}
      array.(inf_array_get) !#l.(data) #i
    {{{ v, RET v; True }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hdata) HΦ".
    wp_load.
    awp_apply (inf_array_get_spec with "[//]") without "HΦ"; first lia.
    iInv "Hinv" as "(%front & %back & %hist & %pub & %priv & %past & %prophs & Hfront & Hback & Hctl₁ & Hfront_auth & >Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
    { iModIntro. rewrite right_id. repeat iExists _. iFrame. done. }
    iModIntro. iSplitL.
    { repeat iExists _. iFrame. done. }
    iIntros "_ HΦ". iApply ("HΦ" with "[//]").
  Qed.
  #[local] Lemma inf_chaselev_deque_get_strong l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p i v :
    {{{
      inv ι (inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock γ_prophet γ_winner ι data p) ∗
      l.(data) ↦□ data ∗
      inf_chaselev_deque_hist_frag γ_hist i v
    }}}
      array.(inf_array_get) !#l.(data) #i
    {{{ RET v; True }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hdata & #Hhist_frag) HΦ".
    wp_load.
    awp_apply (inf_array_get_spec with "[//]") without "HΦ"; first lia.
    iInv "Hinv" as "(%front & %back & %hist & %pub & %priv & %past & %prophs & Hfront & Hback & Hctl₁ & Hfront_auth & >Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    iAssert (◇ ⌜(hist ++ pub) !! i = Some v⌝)%I as "#>%Hlookup".
    { iDestruct "Hstate" as "[(>%Hstate & >Hhist_auth & >%Hhist & _) | [(>%Hstate & >Hhist_auth & >%Hhist & _) | (_ & [(>%Hstate & >Hhist_auth & >%Hhist & _) | (>%Hstate & >Hhist_auth & >%Hhist & _)])]]";
        iModIntro;
        iDestruct (inf_chaselev_deque_hist_agree with "Hhist_auth Hhist_frag") as %?;
        iPureIntro.
      - erewrite lookup_app_l_Some; done.
      - destruct pub as [| w pub]; simpl in *; first lia.
        rewrite (assoc (++) hist [w]). erewrite lookup_app_l_Some; done.
      - rewrite (nil_length_inv pub); last lia. list_simplifier. done.
      - rewrite (nil_length_inv pub); last lia. erewrite lookup_app_l_Some; done.
    }
    iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
    { iModIntro. rewrite right_id. repeat iExists _. iFrame. done. }
    iModIntro. iSplitL.
    { repeat iExists _. iFrame. done. }
    iIntros "_ HΦ".
    rewrite Nat2Z.id decide_True; last eauto using lookup_lt_Some.
    erewrite list_lookup_total_correct; last done.
    iApply ("HΦ" with "[//]").
  Qed.
  Lemma inf_chaselev_deque_steal_spec t ι :
    <<<
      inf_chaselev_deque_inv t ι |
      ∀∀ pub, inf_chaselev_deque_model t pub
    >>>
      inf_chaselev_deque_steal t @ ↑ι
    <<<
      ∃∃ o,
      (⌜pub = [] ∧ o = InjLV #()⌝ ∗ inf_chaselev_deque_model t []) ∨
      (∃ v pub', ⌜pub = v :: pub' ∧ o = SOMEV v⌝ ∗ inf_chaselev_deque_model t pub') |
      RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %γ_prophet & %γ_winner & %data & %p & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hmeta_prophet & #Hmeta_winner & #Hdata & #Hp & #Hinv) HΦ".
    iLöb as "IH".

    wp_rec. wp_pures.

    (* → [NewId] *)
    wp_apply (wp_new_id with "[//]"). iIntros "%id Hid".

    wp_pures.

    (* → [!#l.(front)] *)
    wp_bind (!#l.(front))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front1 & %back1 & %hist & %pub & %priv & %past1 & %prophs1 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    wp_load.
    (* emit front fragment at [front1] *)
    iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
    (* close invariant *)
    iModIntro. iSplitR "Hid HΦ".
    { repeat iExists _. iFrame. done. }
    clear.

    wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front2 & %back2 & %hist & %pub & %priv & %past2 & %prophs2 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & Hprophet_model & >%Hpast & Hstate)".
    wp_load.
    (* we have [front1 ≤ front2] *)
    iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront2.
    (* enforce [front1 < back2] *)
    destruct (decide (front1 < back2)%Z) as [Hbranch1 | Hbranch1]; last first.
    { (* we have [pub = []] *)
      assert (length pub = 0) as ->%nil_length_inv by lia.
      (* begin transaction *)
      iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
      iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
      (* end transation *)
      iMod ("HΦ" with "[Hpub₂] [//]") as "HΦ".
      { iLeft. iSplit; first done. repeat iExists _. naive_solver. }
      (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { repeat iExists _. iFrame. done. }
      clear- Hbranch1.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_false_2; last done.

      wp_pures.

      iApply "HΦ".
    }
    (* enforce [front2 = front1] *)
    rewrite Nat.le_lteq in Hfront2. destruct Hfront2 as [Hbranch2 | <-].
    { (* emit front fragment at [front2] *)
      iClear "Hfront_frag". iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { repeat iExists _. iFrame. done. }
      clear- Hbranch1 Hbranch2.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_true_2; last done.

      wp_pures.

      (* → [array.(inf_array_get) !#l.(data) #front1] *)
      wp_apply (inf_chaselev_deque_get_weak with "[$Hinv $Hdata]"). iIntros "%v _".

      wp_pures.

      (* → [!#l.(prophecy)] *)
      wp_load.

      wp_pures.

      (* → [Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)] *)
      wp_bind (Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)%V).
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & >Hprophet_model & >%Hpast & Hstate)".
      (* do resolve *)
      wp_apply (wise_prophet_resolve_spec with "Hprophet_model"); first done.
      (* CmpXchg must fail as we have seen [front2] such that [front1 < front2] *)
      wp_cmpxchg as [= ->%(inj _)] | _Hbranch3.
      { iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
        lia.
      }
      iAssert ⌜front1 < front3⌝%I as %Hbranch3; last clear _Hbranch3.
      { iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
        iPureIntro. lia.
      }
      iModIntro. iExists (front3, false, front1, id). iSplit; first done. iIntros "%prophs3' -> Hprophet_model".
      (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { iExists front3, back3, hist, pub, priv, (past3 ++ [_]), prophs3'. iFrame.
        iSplit; first done.
        iSplit. { iPureIntro. decompose_Forall; done. }
        iDestruct "Hstate" as "[Hstate | [(%Hstate & Hhist_auth & %Hhist & Hstate) | (Hlock & [(%Hstate & Hhist_auth & %Hhist & Hstate) | Hstate])]]".
        - iLeft. done.
        - iRight. iLeft. iFrame. iSplit; first done. iSplit; first done.
          rewrite /inf_chaselev_deque_state_inner₂ filter_cons_False //. lia.
        - do 2 iRight. iFrame. iLeft. iFrame. iSplit; first done. iSplit; first done.
          rewrite /inf_chaselev_deque_state_inner₃₁ filter_cons_False //. lia.
        - do 2 iRight. iFrame.
      }
      clear- Hbranch1 Hbranch2 Hbranch3.

      wp_pures.

      (* → [inf_chaselev_deque_steal #l] *)
      wp_apply ("IH" with "HΦ").
    }
    (* we are in state 2 *)
    iDestruct "Hstate" as "[(%Hstate & _) | [(_ & Hhist_auth & %Hhist & Hstate) | (_ & [(%Hstate & _) | (%Hstate & _)])]]"; try lia.
    (* hence there is at least one public value *)
    destruct pub as [| v pub]; first naive_solver lia.
    (* emit history fragment at [front1] *)
    iDestruct (inf_chaselev_deque_hist_frag_get front1 v with "Hhist_auth") as "#Hhist_frag".
    { rewrite lookup_app_r; last lia. rewrite Hhist Nat.sub_diag //. }
    (* emit prophet lower bound *)
    iDestruct (wise_prophet_lb_get with "Hprophet_model") as "#Hprophet_lb".
    (* enforce [filter (λ '(_, _, front', _), front' = front1) prophs2 ≠ []] *)
    rewrite /inf_chaselev_deque_state_inner₂. destruct (filter _ prophs2) as [| (((front1' & b) & front1'') & id') prophs2'] eqn:Hbranch2.
    { (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { iExists front1, back2, hist, (v :: pub), priv, past2, prophs2. iFrame.
        iSplit; first done.
        iSplit; first done.
        iRight. iLeft. iFrame. iSplit; first done. iSplit; first done.
        rewrite /inf_chaselev_deque_state_inner₂ Hbranch2 //.
      }
      clear- Hbranch1 Hbranch2.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_true_2; last done.

      wp_pures.

      (* → [array.(inf_array_get) !#l.(data) #front1] *)
      wp_apply (inf_chaselev_deque_get_strong with "[$Hinv $Hdata $Hhist_frag]"). iIntros "_".

      wp_pures.

      (* → [!#l.(prophecy)] *)
      wp_load.

      wp_pures.

      (* → [Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)] *)
      wp_bind (Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)%V).
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & >Hprophet_model & >%Hpast & Hstate)".
      (* current prophecies are a suffix of prophet lower bound *)
      iDestruct (wise_prophet_model_lb_valid with "Hprophet_model Hprophet_lb") as %(past3_1 & past3_2 & -> & ->).
      (* do resolve *)
      wp_apply (wise_prophet_resolve_spec with "Hprophet_model"); first done.
      (* whether CmpXchg succeed or not, we reach a contradiction *)
      wp_cmpxchg as _ | _.
      all: iModIntro; iExists (front3, _, front1, id); iSplit; first done; iIntros "%prophs3' ->".
      all: eelim (filter_nil_not_elem_of _ _ (front3, _, front1, id)); [naive_solver.. |].
      all: apply elem_of_app; right; apply elem_of_cons; left; naive_solver.
    }
    (* enforce [id' = id] *)
    destruct (decide (id' = id)) as [-> | Hbranch3]; first last.
    { (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { iExists front1, back2, hist, (v :: pub), priv, past2, prophs2. iFrame.
        iSplit; first done.
        iSplit; first done.
        iRight. iLeft. iFrame. iSplit; first done. iSplit; first done.
        rewrite /inf_chaselev_deque_state_inner₂ Hbranch2 //.
      }
      clear- Hbranch1 Hbranch2 Hbranch3.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_true_2; last done.

      wp_pures.

      (* → [array.(inf_array_get) !#l.(data) #front1] *)
      wp_apply (inf_chaselev_deque_get_strong with "[$Hinv $Hdata $Hhist_frag]"). iIntros "_".

      wp_pures.

      (* → [!#l.(prophecy)] *)
      wp_load.

      wp_pures.

      (* → [Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)] *)
      wp_bind (Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)%V).
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & >Hprophet_model & >%Hpast & Hstate)".
      (* current prophecies are a suffix of prophet lower bound *)
      iDestruct (wise_prophet_model_lb_valid with "Hprophet_model Hprophet_lb") as %(past3_1 & past3_2 & -> & ->).
      (* do resolve *)
      wp_apply (wise_prophet_resolve_spec with "Hprophet_model"); first done.
      (* CmpXchg must fail as we are not the winner *)
      wp_cmpxchg as [= ->%(inj _)] | _Hbranch4.
      { iModIntro. iExists (front1, true, front1, id). iSplit; first done. iIntros "%prophs3' -> Hprophet_model".
        exfalso. simpl in *.
        rewrite filter_app filter_cons_True // in Hbranch2.
        destruct (filter _ past3_2) as [| ? past3_2'] eqn:Heq; invert Hbranch2.
        eassert ((front1', b, front1'', id') ∈ filter _ past3_2) as Helem.
        { erewrite Heq. constructor. }
        apply elem_of_list_filter in Helem as (-> & Helem).
        rewrite Forall_app !Forall_forall in Hpast. destruct Hpast as (_ & Hpast).
        specialize (Hpast (front1', b, front1, id') Helem). simpl in Hpast. lia.
      }
      iAssert ⌜front1 < front3⌝%I as %Hbranch4; last clear _Hbranch4.
      { iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
        iPureIntro. assert (front1 ≠ front3) by naive_solver. lia.
      }
      iModIntro. iExists (front3, false, front1, id). iSplit; first done. iIntros "%prophs3' -> Hprophet_model".
      (* close invariant *)
      iModIntro. iSplitR "Hid HΦ".
      { iExists front3, back3, hist, pub, priv, _, prophs3'. iFrame.
        iSplit; first done.
        iSplit. { iPureIntro. decompose_Forall; done. }
        iDestruct "Hstate" as "[Hstate | [(%Hstate & Hstate) | (Hlock & [(%Hstate & Hstate) | Hstate])]]".
        - iLeft. done.
        - iRight. iLeft. iFrame. iSplit; first done.
          rewrite /inf_chaselev_deque_state_inner₂ filter_cons_False //. lia.
        - do 2 iRight. iFrame. iLeft. iFrame. iSplit; first done.
          rewrite /inf_chaselev_deque_state_inner₃₁ filter_cons_False //. lia.
        - do 2 iRight. iFrame.
      }
      clear- Hbranch1 Hbranch2 Hbranch3 Hbranch4.

      wp_pures.

      (* → [inf_chaselev_deque_steal #l] *)
      wp_apply ("IH" with "HΦ").
    }
    (* we now know we are the next winner *)
    iDestruct "Hstate" as "[(% & % & % & Hwinner₁ & Hwinner₂) | (Hid' & _)]"; last first.
    { iDestruct (identifier_model_exclusive with "Hid Hid'") as %[]. }
    iMod (inf_chaselev_deque_winner_update front1 Φ with "Hwinner₁ Hwinner₂") as "(Hwinner₁ & Hwinner₂)".
    (* close invariant *)
    iModIntro. iSplitR "Hwinner₂".
    { iExists front1, back2, hist, (v :: pub), priv, past2, prophs2. iFrame.
      iSplit; first done.
      iSplit; first done.
      iRight. iLeft. iFrame. iSplit; first done. iSplit; first done.
      rewrite /inf_chaselev_deque_state_inner₂ Hbranch2. iRight. iFrame. iExists Φ. iFrame.
      iNext. rewrite /inf_chaselev_deque_atomic_update. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%_pub (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-.
      iAaccIntro with "Hpub₂".
      { iIntros "Hpub₂ !>". iSplitL "Hpub₂"; last auto.
        repeat iExists _. iFrame "#∗". done.
      }
      iIntros "%w %pub' (-> & Hpub₂) !>". iExists (SOMEV w). iSplitL.
      - iRight. repeat iExists _. iSplit; first done. repeat iExists _. iFrame "#∗". done.
      - iIntros "HΦ". iApply ("HΦ" with "[//]").
    }
    clear- Hbranch1 Hbranch2.

    wp_pures.

    (* → [if: #(bool_decide (front1 < back2))] *)
    rewrite bool_decide_eq_true_2; last done.

    wp_pures.

    (* → [array.(inf_array_get) !#l.(data) #front1] *)
    wp_apply (inf_chaselev_deque_get_strong with "[$Hinv $Hdata $Hhist_frag]"). iIntros "_".

    wp_pures.

    (* → [!#l.(prophecy)] *)
    wp_load.

    wp_pures.

    (* → [Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)] *)
    wp_bind (Resolve (CmpXchg #l.(front) #front1 #(front1 + 1)) #p (#front1, #id)%V).
    (* open invariant *)
    iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & %past3 & %prophs3 & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & Hpub₁ & >%Hpub & >Hprophet_model & >%Hpast & Hstate)".
    (* we are in state 2 or state 3.1 *)
    iDestruct "Hstate" as "[(_ & _ & _ & Hwinner) | [(>%Hbranch3 & Hhist_auth & >%Hhist & Hstate) | (Hlock & [(><- & Hhist_auth & >%Hhist & Hstate) | (_ & _ & _ & Hwinner)])]]";
      (* do resolve *)
      (wp_apply (wise_prophet_resolve_spec with "Hprophet_model"); first done).

    1,4:
      wp_cmpxchg as _ | _;
      iDestruct (inf_chaselev_deque_winner₂_exclusive with "Hwinner₂ Hwinner") as %[].

    - (* CmpXchg must succeed as we are the next winner *)
      wp_cmpxchg as [= ->%(inj _)] | Hbranch4;
        iDestruct (inf_chaselev_deque_winner₂_state_inner₂ (SOMEV v) with "Hwinner₂ Hstate") as "(%id' & %Φ' & %Heq & HΦ & Hwinner₁ & Hwinner₂ & _ & HΦ')";
        [clear Heq | naive_solver].
      iModIntro. iExists (front1, true, front1, id). iSplit; first done. iIntros "%prophs3' -> Hprophet_model".
      (* update front *)
      iMod (inf_chaselev_deque_front_auth_update (S front1) with "Hfront_auth") as "Hfront_auth"; first lia.
      (* begin transaction *)
      iMod "HΦ'" as "(%_pub & Hpub₂ & _ & HΦ')".
      iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
      (* update public values *)
      destruct pub as [| _v pub]; first naive_solver lia.
      iAssert ⌜_v = v⌝%I as %->.
      { iDestruct (inf_chaselev_deque_hist_agree with "Hhist_auth Hhist_frag") as %Hlookup.
        iPureIntro.
        rewrite lookup_app_r in Hlookup; last lia.
        rewrite list_lookup_singleton_Some in Hlookup. naive_solver.
      }
      iMod (inf_chaselev_deque_pub_update pub with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
      (* end transaction *)
      iMod ("HΦ'" with "[$Hpub₂ //]") as "HΦ'".
      (* close invariant *)
      iSplitR "HΦ HΦ'".
      { simpl in Hpub.
        iExists (S front1), back3, (hist ++ [v]), pub, priv, (past3 ++ [_]), prophs3'. iFrame.
        iSplitL "Hfront". { assert (front1 + 1 = S front1)%Z as -> by lia. done. }
        iSplitL "Hdata_model". { rewrite -(assoc (++)) //. }
        iSplitR; first auto with lia.
        iSplitR.
        { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
          eapply Forall_impl; first done. intros (((? & ?) & ?) & ?) ?. lia.
        }
        destruct pub as [| w pub]; simpl in Hpub.
        - iModIntro. iLeft. iFrame. iSplit; first auto with lia.
          iSplit. { rewrite app_length /=. auto with lia. }
          repeat iExists _. iFrame.
        - iMod (inf_chaselev_deque_hist_update w with "Hhist_auth") as "Hhist_auth".
          iModIntro. iRight. iLeft. iFrame. iSplit; first auto with lia.
          iSplit. { rewrite app_length /=. auto with lia. }
          rewrite /inf_chaselev_deque_state_inner₂. destruct (filter _ prophs3') as [| (((? & ?) & ?) & ?) ?].
          + repeat iExists _. iFrame.
          + iLeft. repeat iExists _. iFrame.
      }
      iModIntro.
      clear- Hbranch1 Hbranch2 Hbranch3.

      wp_pures.

      iRewrite- "HΦ". done.

    - (* CmpXchg must succeed as we are the next winner *)
      wp_cmpxchg as [= ->%(inj _)] | Hbranch4;
          iDestruct (inf_chaselev_deque_winner₂_state_inner₃₁ (SOMEV v) with "Hwinner₂ Hstate") as "(%id' & %Φ' & %Heq & HΦ & Hwinner₁ & Hwinner₂ & _ & HΦ')";
        [clear Heq | naive_solver].
      iModIntro. iExists (front1, true, front1, id). iSplit; first done. iIntros "%prophs3' -> Hprophet_model".
      (* we know there is no public values and [hist !!! front1 = v] *)
      destruct (nil_or_length_pos pub) as [-> |]; last lia.
      iAssert ⌜hist !!! front1 = v⌝%I as %->.
      { iDestruct (inf_chaselev_deque_hist_agree with "Hhist_auth Hhist_frag") as %Hlookup.
        iPureIntro. apply list_lookup_total_correct. done.
      }
      (* update front *)
      iMod (inf_chaselev_deque_front_auth_update (S front1) with "Hfront_auth") as "Hfront_auth"; first lia.
      (* close invariant *)
      iModIntro. iSplitR "HΦ HΦ'".
      { iExists (S front1), front1, hist, [], priv, (past3 ++ [_]), prophs3'. iFrame.
        iSplitL "Hfront". { assert (front1 + 1 = S front1)%Z as -> by lia. done. }
        iSplit; first auto with lia.
        iSplitR.
        { iPureIntro. rewrite Forall_app Forall_singleton. split; last lia.
          eapply Forall_impl; first done. intros (((? & ?) & ?) & ?) ?. lia.
        }
        do 2 iRight. iFrame. iRight. iSplit; first auto with lia. iSplit; first done.
        repeat iExists _. iFrame.
      }
      clear- Hbranch1 Hbranch2.

      wp_pures.

      iRewrite- "HΦ". done.
  Qed.

  Lemma inf_chaselev_deque_pop_spec t ι :
    <<<
      inf_chaselev_deque_inv t ι ∗
      inf_chaselev_deque_owner t |
      ∀∀ pub, inf_chaselev_deque_model t pub
    >>>
      inf_chaselev_deque_pop t @ ↑ι
    <<<
      ∃∃ o,
      (⌜pub = [] ∧ o = NONEV⌝ ∗ inf_chaselev_deque_model t []) ∨
      (∃ pub' v, ⌜pub = pub' ++ [v] ∧ o = SOMEV v⌝ ∗ inf_chaselev_deque_model t pub') |
      RET o; inf_chaselev_deque_owner t
    >>>.
  Proof.
  Admitted.

  Lemma inf_chaselev_deque_unboxed t ι :
    inf_chaselev_deque_inv t ι -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %γ_prophet & %γ_winner & %data & %p & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hmeta_prophet & #Hmeta_winner & #Hdata & #Hp & #Hinv) //".
  Qed.

  Program Definition inf_chaselev_ws_deque : ws_deque Σ true := {|
    ws_deque_make :=
      inf_chaselev_deque_make ;
    ws_deque_push :=
      inf_chaselev_deque_push ;
    ws_deque_pop :=
      inf_chaselev_deque_pop ;
    ws_deque_steal :=
      inf_chaselev_deque_steal ;

    ws_deque_name :=
      unit ;
    ws_deque_inv t _ ι :=
      inf_chaselev_deque_inv t ι ;
    ws_deque_model t _ vs :=
      inf_chaselev_deque_model t vs ;
    ws_deque_owner t _ :=
      inf_chaselev_deque_owner t ;
  |}.
  Next Obligation.
    simpl. eauto using inf_chaselev_deque_owner_exclusive.
  Qed.
  Next Obligation.
    iIntros "%ι %Φ _ HΦ".
    wp_apply (inf_chaselev_deque_make_spec with "[//]"). iIntros "%t".
    iApply ("HΦ" $! t ()).
  Qed.
  Next Obligation.
    simpl. eauto using inf_chaselev_deque_push_spec.
  Qed.
  Next Obligation.
    simpl. eauto using inf_chaselev_deque_pop_spec.
  Qed.
  Next Obligation.
    simpl. eauto using inf_chaselev_deque_steal_spec.
  Qed.
  Next Obligation.
    simpl. eauto using inf_chaselev_deque_unboxed.
  Qed.
End inf_chaselev_deque_G.

#[global] Opaque inf_chaselev_deque_make.
#[global] Opaque inf_chaselev_deque_push.
#[global] Opaque inf_chaselev_deque_steal.
#[global] Opaque inf_chaselev_deque_pop.

#[global] Opaque inf_chaselev_deque_inv.
#[global] Opaque inf_chaselev_deque_model.
#[global] Opaque inf_chaselev_deque_owner.
End base.

Program Definition inf_chaselev_ws_deque `{!heapGS Σ} {array} `{inf_chaselev_deque_G : !InfChaselevDequeG Σ array} : ws_deque Σ true := {|
  ws_deque_make :=
    base.inf_chaselev_ws_deque.(ws_deque_make) ;
  ws_deque_push :=
    λ: "t" "v",
      base.inf_chaselev_ws_deque.(ws_deque_push) "t" (ref "v") ;
  ws_deque_pop :=
    λ: "t",
      match: base.inf_chaselev_ws_deque.(ws_deque_pop) "t" with
        NONE => NONE
      | SOME "ref" => SOME (!"ref")
      end ;
  ws_deque_steal :=
    λ: "t",
      match: base.inf_chaselev_ws_deque.(ws_deque_steal) "t" with
        NONE => NONE
      | SOME "ref" => SOME (!"ref")
      end ;

  ws_deque_name :=
    base.inf_chaselev_ws_deque.(ws_deque_name) ;
  ws_deque_inv :=
    base.inf_chaselev_ws_deque.(ws_deque_inv) ;
  ws_deque_model t γ vs := (
    ∃ ls,
    base.inf_chaselev_ws_deque.(ws_deque_model) t γ (LitV ∘ LitLoc <$> ls) ∗
    [∗ list] l; v ∈ ls; vs, l ↦ v
  )%I ;
  ws_deque_owner :=
    base.inf_chaselev_ws_deque.(ws_deque_owner) ;
|}.
Next Obligation.
  eauto using base.inf_chaselev_ws_deque.(ws_deque_owner_exclusive).
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  wp_apply (base.inf_chaselev_ws_deque.(ws_deque_make_spec) with "[//]"). iIntros "%t %γ (#Hinv & Hmodel & Howner)".
  iApply "HΦ". iFrame "#∗". iExists []. naive_solver.
Qed.
Next Obligation.
  iIntros "* !> %Φ (#Hinv & Howner) HΦ".
  wp_pures. wp_alloc l as "Hl".
  awp_apply (base.inf_chaselev_ws_deque.(ws_deque_push_spec) with "[$Hinv $Howner]").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel"; iIntros "Hmodel !>".
  - iFrame. iSplitL; auto with iFrame.
  - iRight. iSplitL; last naive_solver.
    iExists (ls ++ [l]). rewrite -fmap_snoc. iFrame. done.
Qed.
Next Obligation.
  iIntros "* !> %Φ (#Hinv & Howner) HΦ".
  wp_pures.
  awp_apply (base.inf_chaselev_ws_deque.(ws_deque_pop_spec) with "[$Hinv $Howner]").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel".
  - iIntros "Hmodel !>". iFrame. iSplitL; auto with iFrame.
  - iIntros "% [((%Heq & ->) & Hmodel) | (%ws & %w & (%Heq & ->) & Hmodel)] !>"; iRight.
    + apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hls") as %->.
      iExists NONEV. iSplitL; first naive_solver. iIntros "HΦ !> Howner".
      wp_pures.
      iApply ("HΦ" with "Howner").
    + generalize dependent ls. refine (rev_ind _ _ _); [intros Heq | intros l ls _ Heq].
      { rewrite fmap_nil in Heq. edestruct app_cons_not_nil. done. }
      rewrite fmap_app app_inj_tail_iff in Heq. destruct Heq as (<- & <-).
      generalize dependent vs. apply rev_ind; [| intros v vs _].
      { iDestruct (big_sepL2_nil_inv_r with "Hls") as %?.
        edestruct app_cons_not_nil. done.
      }
      iDestruct (big_sepL2_snoc with "Hls") as "(Hls & Hl)".
      iExists (SOMEV v). iSplitR "Hl".
      * iRight. auto with iFrame.
      * iIntros "HΦ !> Howner".
        wp_pures. wp_load. wp_pures.
        iApply ("HΦ" with "Howner").
Qed.
Next Obligation.
  iIntros "* !> %Φ #Hinv HΦ".
  wp_pures.
  awp_apply (base.inf_chaselev_ws_deque.(ws_deque_steal_spec) with "Hinv").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel".
  - iIntros "Hmodel !>". iFrame. iSplitL; auto with iFrame.
  - iIntros "% [((%Heq & ->) & Hmodel) | (%w & %ws & (%Heq & ->) & Hmodel)] !>"; iRight.
    + apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hls") as %->.
      iExists NONEV. iSplitL; first naive_solver. iIntros "HΦ !> _".
      wp_pures.
      iApply ("HΦ" with "[//]").
    + destruct ls as [| l ls]; simplify.
      destruct vs as [| v vs].
      { iDestruct (big_sepL2_nil_inv_r with "Hls") as %?. simplify. }
      iDestruct (big_sepL2_cons with "Hls") as "(Hl & Hls)".
      iExists (SOMEV v). iSplitR "Hl".
      * iRight. auto with iFrame.
      * iIntros "HΦ !> Howner".
        wp_pures. wp_load. wp_pures.
        iApply ("HΦ" with "Howner").
Qed.
Next Obligation.
  simpl. intros. unshelve iApply base.inf_chaselev_ws_deque.(ws_deque_unboxed). done.
Qed.
