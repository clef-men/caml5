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
  notations
  proofmode.
From caml5.std Require Import
  inf_array.
From caml5.concurrent Require Export
  base.

Class InfChaselevDequeG Σ `{!heapGS Σ} (array : inf_array Σ false) := {
  inf_chaselev_deque_G_ctl_G : AuthExclG Σ (prodO ZO (nat -d> valO)) ;
  inf_chaselev_deque_G_front_G : AuthNatMaxG Σ ;
  inf_chaselev_deque_G_hist_G : mono_listG val Σ ;
  inf_chaselev_deque_G_pub_G : AuthExclG Σ (listO valO) ;
  inf_chaselev_deque_G_lock_G : ExclG Σ unitO ;
}.
#[local] Existing Instance inf_chaselev_deque_G_ctl_G.
#[local] Existing Instance inf_chaselev_deque_G_front_G.
#[local] Existing Instance inf_chaselev_deque_G_hist_G.
#[local] Existing Instance inf_chaselev_deque_G_pub_G.
#[local] Existing Instance inf_chaselev_deque_G_lock_G.

Definition inf_chaselev_deque_Σ := #[
  auth_excl_Σ (prodO ZO (nat -d> valO)) ;
  auth_nat_max_Σ ;
  mono_listΣ val ;
  auth_excl_Σ (listO valO) ;
  excl_Σ unitO
].
Lemma subG_inf_chaselev_deque_Σ Σ `{!heapGS Σ} array :
  subG inf_chaselev_deque_Σ Σ →
  InfChaselevDequeG Σ array.
Proof.
  solve_inG.
Qed.

Section inf_chaselev_deque_G.
  Context `{!heapGS Σ} {array} `{!InfChaselevDequeG Σ array}.
  Implicit Types front : nat.
  Implicit Types back : Z.
  Implicit Types l : loc.
  Implicit Types v t data : val.
  Implicit Types hist pub : list val.
  Implicit Types priv : nat → val.

  Notation "t '.(front)'" := t.(0)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(back)'" := t.(1)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(data)'" := t.(2)%stdpp
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

  Definition inf_chaselev_deque_make : val :=
    λ: <>,
      let: "t" := AllocN #3 #0 in
      "t".(data) <- array.(inf_array_make) #() ;;
      "t".

  Definition inf_chaselev_deque_push : val :=
    λ: "t" "v",
      let: "back" := !"t".(back) in
      let: "data" := !"t".(data) in
      array.(inf_array_set) "data" "back" "v" ;;
      "t".(back) <- "back" + #1.

  Definition inf_chaselev_deque_steal : val :=
    rec: "inf_chaselev_deque_steal" "t" :=
      let: "front" := !"t".(front) in
      let: "back" := !"t".(back) in
      let: "data" := !"t".(data) in
      if: "front" < "back" then (
        let: "v" := array.(inf_array_get) "data" "front" in
        if: CAS "t".(front) "front" ("front" + #1) then (
          SOME "v"
        ) else (
          "inf_chaselev_deque_steal" "t"
        )
      ) else (
        NONE
      ).

  Definition inf_chaselev_deque_pop : val :=
    λ: "t",
      let: "back" := !"t".(back) - #1 in
      let: "data" := !"t".(data) in
      "t".(back) <- "back" ;;
      let: "front" := !"t".(front) in
      if: "back" < "front" then (
        "t".(back) <- "front" ;;
        NONE
      ) else (
        let: "v" := array.(inf_array_get) "data" "back" in
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

  Notation inf_chaselev_deque_meta_ctl := (nroot .@ "ctl").
  Notation inf_chaselev_deque_meta_front := (nroot .@ "front").
  Notation inf_chaselev_deque_meta_hist := (nroot .@ "hist").
  Notation inf_chaselev_deque_meta_pub := (nroot .@ "pub").
  Notation inf_chaselev_deque_meta_lock := (nroot .@ "lock").

  #[local] Definition inf_chaselev_deque_ctl₁ γ_ctl back priv :=
    @auth_excl_auth _ _ inf_chaselev_deque_G_ctl_G γ_ctl (DfracOwn 1) (back, priv).
  #[local] Definition inf_chaselev_deque_ctl₂ γ_ctl back priv :=
    @auth_excl_frag _ _ inf_chaselev_deque_G_ctl_G γ_ctl (back, priv).

  #[local] Definition inf_chaselev_deque_front_auth γ_front front :=
    auth_nat_max_auth γ_front (DfracOwn 1) front.
  #[local] Definition inf_chaselev_deque_front_frag γ_front front :=
    auth_nat_max_frag γ_front front.

  #[local] Definition inf_chaselev_deque_hist_auth γ_hist hist pub :=
    mono_list_auth γ_hist 1
      match pub with
      | [] => hist
      | v :: _ => hist ++ [v]
      end.
  #[local] Definition inf_chaselev_deque_hist_frag γ_hist i v :=
    mono_list_mapsto γ_hist i v.

  #[local] Definition inf_chaselev_deque_pub₁ γ_pub pub :=
    @auth_excl_frag _ _ inf_chaselev_deque_G_pub_G γ_pub pub.
  #[local] Definition inf_chaselev_deque_pub₂ γ_pub pub :=
    @auth_excl_auth _ _ inf_chaselev_deque_G_pub_G γ_pub (DfracOwn 1) pub.

  #[local] Definition inf_chaselev_deque_lock γ_lock :=
    excl γ_lock ().

  #[local] Definition inf_chaselev_deque_state₁ front back pub : iProp Σ :=
    ⌜(front ≤ back)%Z ∧ length pub = Z.to_nat (back - front)⌝.
  #[local] Definition inf_chaselev_deque_state₂₁ front back pub : iProp Σ :=
    ⌜back = front ∧ length pub = 1⌝.
  #[local] Definition inf_chaselev_deque_state₂₂ front back pub : iProp Σ :=
    ⌜Z.of_nat front = (back + 1)%Z ∧ pub = []⌝.
  #[local] Definition inf_chaselev_deque_state₂ γ_lock front back pub : iProp Σ :=
    inf_chaselev_deque_lock γ_lock ∗
    (inf_chaselev_deque_state₂₁ front back pub ∨ inf_chaselev_deque_state₂₂ front back pub).
  #[local] Definition inf_chaselev_deque_state γ_lock front back pub : iProp Σ :=
    inf_chaselev_deque_state₁ front back pub ∨
    inf_chaselev_deque_state₂ γ_lock front back pub.

  #[local] Definition inf_chaselev_deque_data_model data hist pub priv :=
    array.(inf_array_model) data (
      λ i,
        let vs := hist ++ pub in
        if decide (i < length vs) then vs !!! i else priv (i - length vs)
    ).

  #[local] Definition inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock data : iProp Σ :=
    ∃ front back hist pub priv,
    (* physical fields *)
    l.(front) ↦ #front ∗ l.(back) ↦ #back ∗
    (* control token *)
    inf_chaselev_deque_ctl₁ γ_ctl back priv ∗
    (* front authority *)
    inf_chaselev_deque_front_auth γ_front front ∗
    (* data model *)
    inf_chaselev_deque_data_model data hist pub priv ∗
    (* history values *)
    ⌜length hist = front⌝ ∗
    inf_chaselev_deque_hist_auth γ_hist hist pub ∗
    (* public values *)
    inf_chaselev_deque_pub₁ γ_pub pub ∗
    (* state *)
    inf_chaselev_deque_state γ_lock front back pub.
  Definition inf_chaselev_deque_inv t ι : iProp Σ :=
    ∃ l γ_ctl γ_front γ_hist γ_pub γ_lock data,
    ⌜t = #l⌝ ∗
    (* metas *)
    meta l inf_chaselev_deque_meta_ctl γ_ctl ∗
    meta l inf_chaselev_deque_meta_front γ_front ∗
    meta l inf_chaselev_deque_meta_hist γ_hist ∗
    meta l inf_chaselev_deque_meta_pub γ_pub ∗
    meta l inf_chaselev_deque_meta_lock γ_lock ∗
    (* physical fields *)
    l.(data) ↦□ data ∗
    (* invariant *)
    inv ι (inf_chaselev_deque_inv_inner l γ_ctl γ_front γ_hist γ_pub γ_lock data).

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

  #[global] Instance inf_chaselev_deque_inv_persistent t ι :
    Persistent (inf_chaselev_deque_inv t ι).
  Proof.
    apply _.
  Qed.
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

  #[local] Lemma inf_chaselev_deque_ctl_alloc :
    ⊢ |==> ∃ γ_ctl,
      inf_chaselev_deque_ctl₁ γ_ctl 0 (λ _, #()) ∗
      inf_chaselev_deque_ctl₂ γ_ctl 0 (λ _, #()).
  Proof.
    iMod (auth_excl_alloc' (auth_excl_G := inf_chaselev_deque_G_ctl_G) ((0%Z, λ _, #()) : prodO ZO (nat -d> valO))) as "(%γ_ctl & Hctl₁ & Hctl₂)".
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

  (* TODO: hist lemmas *)
  #[local] Lemma inf_chaselev_deque_hist_alloc :
    ⊢ |==> ∃ γ_hist,
      inf_chaselev_deque_hist_auth γ_hist [] [].
  Proof.
    iMod (mono_list_alloc []) as "(%γ_hist & Hhist_auth & _)".
    iExists γ_hist. done.
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
  #[local] Lemma inf_chaselev_deque_lock_state γ_lock front back pub :
    inf_chaselev_deque_lock γ_lock -∗
    inf_chaselev_deque_state γ_lock front back pub -∗
    inf_chaselev_deque_state₁ front back pub.
  Proof.
    iIntros "Hlock [Hstate | (Hlock' & Hstate)]"; first done.
    iDestruct (inf_chaselev_deque_lock_exclusive with "Hlock Hlock'") as %[].
  Qed.

  Lemma inf_chaselev_deque_owner_exclusive t :
    inf_chaselev_deque_owner t -∗
    inf_chaselev_deque_owner t -∗
    False.
  Proof.
    iIntros "(%l1 & %γ_ctl1 & %γ_lock1 & %back1 & %priv1 & %Heq1 & #Hmeta_ctl1 & #Hmeta_lock1 & Hctl₂1 & Hlock1) (%l2 & %γ_ctl2 & %γ_lock2 & %back2 & %priv2 & %Heq2 & #Hmeta_ctl2 & #Hmeta_lock2 & Hctl₂2 & Hlock2)". simplify.
    iDestruct (meta_agree with "Hmeta_lock1 Hmeta_lock2") as %->.
    iApply (inf_chaselev_deque_lock_exclusive with "Hlock1 Hlock2").
  Qed.

  Lemma inf_chaselev_deque_make_spec ι :
    {{{ True }}}
      inf_chaselev_deque_make #()
    {{{ t,
      RET t;
      inf_chaselev_deque_inv t ι ∗ inf_chaselev_deque_model t [] ∗ inf_chaselev_deque_owner t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (Hl & (Hmeta & _))".
    iDestruct (array_cons with "Hl") as "(Hfront & Hl)".
    iDestruct (array_cons with "Hl") as "(Hback & Hl)".
    iDestruct (array_cons with "Hl") as "(Hdata & _)".
    rewrite loc_add_0 -{2}(loc_add_0 l) loc_add_assoc /=. assert (1 + 1 = 2)%Z as -> by lia.
    wp_pures.
    wp_apply (inf_array_make_spec with "[//]"). iIntros "%data Hdata_model".
    wp_pures. wp_store.
    iMod (mapsto_persist with "Hdata") as "#Hdata".
    iApply "HΦ".
    iMod inf_chaselev_deque_ctl_alloc as "(%γ_ctl & Hctl₁ & Hctl₂)".
    iMod inf_chaselev_deque_front_alloc as "(%γ_front & Hfront_auth)".
    iMod inf_chaselev_deque_hist_alloc as "(%γ_hist & Hhist_auth)".
    iMod inf_chaselev_deque_pub_alloc as "(%γ_pub & Hpub₁ & Hpub₂)".
    iMod inf_chaselev_deque_lock_alloc as "(%γ_lock & Hlock)".
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_ctl) with "Hmeta") as "(Hmeta_ctl & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_front) with "Hmeta") as "(Hmeta_front & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_hist) with "Hmeta") as "(Hmeta_hist & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_pub) with "Hmeta") as "(Hmeta_pub & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑inf_chaselev_deque_meta_lock) with "Hmeta") as "(Hmeta_lock & Hmeta)"; first solve_ndisj.
    iMod (meta_set _ _ γ_ctl with "Hmeta_ctl") as "#Hmeta_ctl"; first done.
    iMod (meta_set _ _ γ_front with "Hmeta_front") as "#Hmeta_front"; first done.
    iMod (meta_set _ _ γ_hist with "Hmeta_hist") as "#Hmeta_hist"; first done.
    iMod (meta_set _ _ γ_pub with "Hmeta_pub") as "#Hmeta_pub"; first done.
    iMod (meta_set _ _ γ_lock with "Hmeta_lock") as "#Hmeta_lock"; first done.
    iSplitR "Hctl₂ Hpub₂ Hlock".
    { iExists l, γ_ctl, γ_front, γ_hist, γ_pub, γ_lock, data. iFrame "∗#". iSplitR; first done.
      iApply inv_alloc. iNext. iExists 0, 0%Z, [], [], (λ _, #()). iFrame.
      iSplit; first done.
      iLeft. naive_solver.
    }
    iSplitL "Hpub₂".
    { iExists l, γ_pub. naive_solver. }
    iExists l, γ_ctl, γ_lock, 0%Z, (λ _, #()). iFrame "∗#". done.
  Qed.

  Lemma inf_chaselev_deque_push_spec t ι v :
    <<<
      inf_chaselev_deque_inv t ι ∗ inf_chaselev_deque_owner t |
      ∀∀ pub, inf_chaselev_deque_model t pub
    >>>
      inf_chaselev_deque_push t v @ ↑ι
    <<<
      inf_chaselev_deque_model t (pub ++ [v]) |
      RET #(); inf_chaselev_deque_owner t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %data & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hdata & #Hinv) & (%l' & %_γ_ctl & %_γ_lock & %back & %priv & %Heq & #_Hmeta_ctl & #_Hmeta_lock & Hctl₂ & Hlock)) HΦ".
    injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_ctl _Hmeta_ctl") as %<-. iClear "_Hmeta_ctl".
    iDestruct (meta_agree with "Hmeta_lock _Hmeta_lock") as %<-. iClear "_Hmeta_lock".

    wp_rec. wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front.
    (* do load [back] *)
    wp_load.
    (* we have lock, hence we are in state 1 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %Hstate.
    (* hence, [0 ≤ back] *)
    assert (0 ≤ back)%Z as Hback by lia.
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { repeat iExists _. iFrame. done. }
    clear- Hback.

    wp_pures.

    (* → [!#l.(data)] *)
    wp_load.

    wp_pures.

    (* → [array.(inf_array_set) data #back v] *)
    awp_apply (inf_array_set_spec with "[//]") without "HΦ"; first done.
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & >Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & >Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front.
    iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
    { iModIntro. iFrame. repeat iExists _. iFrame. done. }
    (* update [priv] in control tokens *)
    set (priv' := <[0 := v]> priv).
    iMod (inf_chaselev_deque_ctl_update back priv' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
    (* we have lock, hence we are in state 1 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %(Hstate & Hpub).
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { iNext. iExists front, back, hist, pub, priv'. iFrame. iSplit; last done.
      (* update data *)
      iApply (inf_array_model_proper with "Hdata_model").
      intros i. rewrite app_length Hhist Hpub.
      assert (front + Z.to_nat (back - front) = Z.to_nat back) as -> by lia.
      destruct (Nat.lt_total i (Z.to_nat back)) as [| [-> |]].
      - rewrite fn_lookup_insert_ne; last lia.
        rewrite !decide_True //.
      - rewrite fn_lookup_insert decide_False; last lia.
        rewrite Nat.sub_diag //.
      - rewrite fn_lookup_insert_ne; last lia.
        rewrite !decide_False; [| lia..].
        rewrite /priv' fn_lookup_insert_ne //. lia.
    }
    iIntros "_ HΦ".
    clear- Hback.

    wp_pures.

    (* → [#l.(back) <- #(back + 1)] *)
    (* open invariant *)
    iInv "Hinv" as "(%front & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front.
    (* do increment [back] *)
    wp_store.
    (* update [priv] in control tokens *)
    set (priv'' := λ i, priv (S i)).
    iMod (inf_chaselev_deque_ctl_update (back + 1) priv'' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
    (* begin transaction *)
    iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & _Hmeta_pub & Hpub₂) & _ & HΦ)".
    injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
    iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
    (* update [pub] *)
    set (pub' := pub ++ [v]).
    iMod (inf_chaselev_deque_pub_update pub' with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
    (* end transaction *)
    iMod ("HΦ" with "[Hpub₂]") as "HΦ".
    { iExists l, γ_pub. iFrame "∗#". done. }
    (* update [hist] *)
    iAssert (inf_chaselev_deque_hist_auth γ_hist hist pub')%I with "[>Hhist_auth]" as "Hhist_auth".
    { destruct pub; last done.
      iMod (mono_list_auth_update_app [v] with "Hhist_auth") as "($ & _)". done.
    }
    (* we have lock, hence we are in state 1 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %(Hstate & Hpub).
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { iNext. iExists front, (back + 1)%Z, hist, pub', priv''. iFrame.
      iSplitL "Hdata_model".
      { (* update data *)
        iApply (inf_array_model_proper with "Hdata_model").
        intros i. rewrite /= !app_length /=.
        destruct (Nat.lt_total i (length hist + length pub)) as [| [-> |]].
        - rewrite !decide_True; [| lia..].
          rewrite assoc lookup_total_app_l //. solve_length.
        - rewrite decide_True; last lia.
          rewrite decide_False; last lia.
          rewrite Nat.sub_diag /priv' fn_lookup_insert.
          rewrite assoc lookup_total_app_r; last solve_length.
          rewrite app_length Nat.sub_diag //.
        - rewrite !decide_False; [| lia..].
          rewrite /priv' fn_lookup_insert_ne; last lia.
          rewrite /priv''. f_equal. lia.
      }
      repeat iSplit; try done.
      (* update state *)
      iLeft. iPureIntro. split; [lia | rewrite app_length Hpub /=; lia].
    }
    clear.

    iApply "HΦ". repeat iExists _. iFrame "∗#". done.
  Qed.

  Lemma inf_chaselev_deque_steal_spec t ι :
    <<<
      inf_chaselev_deque_inv t ι |
      ∀∀ pub, inf_chaselev_deque_model t pub
    >>>
      inf_chaselev_deque_steal t @ ↑ι
    <<<
      ∃∃ o,
      (⌜length pub ≤ 1 ∧ o = NONEV⌝ ∗ inf_chaselev_deque_model t pub) ∨
      (∃ pub' v, ⌜pub = v :: pub' ∧ o = SOMEV v⌝ ∗ inf_chaselev_deque_model t pub') |
      RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %data & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hdata & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    (* → [!#l.(front)] *)
    wp_bind (!#l.(front))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front1 & %back1 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    wp_load.
    (* emit front fragment at [front1] *)
    iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { repeat iExists _. iFrame. done. }
    clear.

    wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front2 & %back2 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    wp_load.
    (* enforce [front1 < back2] *)
    destruct (decide (front1 < back2)%Z) as [Hbr1 | Hbr1]; last first.
    { (* we have [1 ≤ length pub] *)
      iAssert ⌜length pub ≤ 1⌝%I as %Hpub.
      { iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]".
        - iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
          destruct (decide (back2 = front1)) as [-> |]; last lia.
          assert (front1 = front2) as <- by lia. iPureIntro. lia.
        - iPureIntro. lia.
        - simplify. auto.
      }
      (* begin transaction *)
      iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
      iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
      (* end transation *)
      iMod ("HΦ" with "[Hpub₂] [//]") as "HΦ".
      { iLeft. iSplit; first done. repeat iExists _. naive_solver. }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      clear- Hbr1.

      wp_pures.

      (* → [!#l.(data)] *)
      wp_load.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_false_2; last done.

      wp_pures.

      iApply "HΦ".
    }
    (* we have [front1 ≤ front2] *)
    iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hbr2.
    (* enforce [front2 = front1] *)
    rewrite Nat.le_lteq in Hbr2. destruct Hbr2 as [Hbr2 | <-].
    { (* emit front fragment at [front2] *)
      iClear "Hfront_frag".
      iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      clear- Hbr1 Hbr2.

      wp_pures.

      (* → [!#l.(data)] *)
      wp_load.

      wp_pures.

      (* → [if: #(bool_decide (front1 < back2))] *)
      rewrite bool_decide_eq_true_2; last done.

      wp_pures.

      (* → [array.(inf_array_get) data #front1] *)
      awp_apply (inf_array_get_spec with "[//]")  without "HΦ"; first lia.
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & >Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
      { iModIntro. rewrite right_id. repeat iExists _. iFrame. done. }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      iIntros "_ HΦ".
      remember (if decide _ then _ else _) as v.
      clear- Hbr1 Hbr2.

      wp_pures.

      (* → [CmpXchg #l.(front) #front1 #(front1 + 1)] *)
      wp_bind (CmpXchg #l.(front) #front1 #(front1 + 1)).
      (* open invariant *)
      iInv "Hinv" as "(%front4 & %back4 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      (* CAS must fail as we have seen [front2] such that [front1 < front2] *)
      wp_cmpxchg as ? | _.
      { simplify- front1.
        iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
        lia.
      }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }

      wp_pures.

      (* → [inf_chaselev_deque_steal #l] *)
      wp_apply ("HLöb" with "HΦ").
    }
    (* we are in state 1, hence [length pub = back2 - front1] *)
    iAssert ⌜length pub = Z.to_nat (back2 - front1)⌝%I as %Hpub.
    { iDestruct "Hstate" as "[% | (_ & [% | %])]"; [naive_solver | lia..]. }
    (* hence, [pub] contains at least one value *)
    destruct pub as [| v pub]; first naive_solver lia.
    (* emit history fragment at [front1] *)
    iAssert (inf_chaselev_deque_hist_frag γ_hist front1 v) as "#Hhist_frag".
    { iDestruct (mono_list_lb_get with "Hhist_auth") as "#Hhist_frag".
      iApply (mono_list_mapsto_get with "Hhist_frag").
      rewrite lookup_app_r; last lia.
      rewrite Hhist Nat.sub_diag //.
    }
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { repeat iExists _. iFrame. done. }
    clear- Hbr1.

    wp_pures.

    (* → [!#l.(data)] *)
    wp_load.

    wp_pures.

    (* → [if: #(bool_decide (front1 < back2))] *)
    rewrite bool_decide_eq_true_2; last done.

    wp_pures.

    (* → [array.(inf_array_get) data #front1] *)
    awp_apply (inf_array_get_spec with "[//]") without "HΦ"; first lia.
    (* open invariant *)
    iInv "Hinv" as "(%front3 & %back3 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & >Hfront_auth & >Hdata_model & >%Hhist & >Hhist_auth & Hpub₁ & Hstate)".
    iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
    { iModIntro. rewrite right_id. repeat iExists _. iFrame. done. }
    (* we have [front1 < front3] *)
    iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hbr3.
    (* enforce [front3 = front1] *)
    rewrite Nat.le_lteq in Hbr3. destruct Hbr3 as [Hbr3 | <-].
    { (* emit front fragment at [front3] *)
      iClear "Hfront_frag".
      iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      iIntros "_ HΦ".
      remember (if decide _ then _ else _) as w.
      clear- Hbr1 Hbr3.

      wp_pures.

      (* → [CmpXchg #l.(front) #front1 #(front1 + 1)] *)
      wp_bind (CmpXchg #l.(front) #front1 #(front1 + 1)).
      (* open invariant *)
      iInv "Hinv" as "(%front4 & %back4 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      (* CAS must fail as we have seen [front3] such that [front1 < front3] *)
      wp_cmpxchg as ? | _.
      { simplify- front1.
        iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
        lia.
      }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }

      wp_pures.

      (* → [inf_chaselev_deque_steal #l] *)
      wp_apply ("HLöb" with "HΦ").
    }
    (* from history fragment at [front1], we know the loaded value is [v] *)
    iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hhist_lookup.
    replace (if decide _ then _ else _) with v; last first.
    { destruct pub as [| w pub].
      { rewrite list_lookup_alt in Hhist_lookup. lia. }
      rewrite lookup_app_r in Hhist_lookup; last lia.
      apply list_lookup_singleton_Some in Hhist_lookup as (_ & ->).
      rewrite decide_True; last first.
      { rewrite app_length /=. lia. }
      rewrite lookup_total_app_r; last lia.
      rewrite Nat2Z.id Hhist Nat.sub_diag //.
    }
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { repeat iExists _. iFrame. done. }
    iIntros "_ HΦ".
    clear- Hbr1.

    wp_pures.

    (* → [CmpXchg #l.(front) #front1 #(front1 + 1)] *)
    wp_bind (CmpXchg #l.(front) #front1 #(front1 + 1)).
    (* open invariant *)
    iInv "Hinv" as "(%front4 & %back4 & %hist & %pub & %priv & Hfront & Hback & Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    (* begin transaction *)
    iMod "HΦ" as "(%_pub & Hmodel & HΦ)".
    wp_cmpxchg as ? | _; first last.
    { (* abort transation *)
      iMod ("HΦ" with "Hmodel") as "HΦ". iModIntro.
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }

      wp_pures.

      (* → [inf_chaselev_deque_steal #l] *)
      wp_apply ("HLöb" with "HΦ").
    }
    simplify- front1.
    iDestruct "Hmodel" as "(%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂)".
    injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
    iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
    (* [front] has not changed, hence [v] is still the front public value *)
    iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hhist_lookup.
    destruct pub as [| w pub].
    { rewrite list_lookup_alt in Hhist_lookup. lia. }
    rewrite lookup_app_r in Hhist_lookup; last lia.
    apply list_lookup_singleton_Some in Hhist_lookup as (_ & ->).
    (* end transation *)
    iMod (inf_chaselev_deque_pub_update pub with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
    iAssert (inf_chaselev_deque_model #l pub) with "[Hpub₂]" as "Hmodel".
    { iExists l, γ_pub. naive_solver. }
    iMod ("HΦ" with "[Hmodel] [//]") as "HΦ"; first eauto. iModIntro.
    (* update front authority *)
    iMod (inf_chaselev_deque_front_auth_update (S front1) with "Hfront_auth") as "Hfront_auth"; first lia.
    (* update [hist] *)
    iAssert (inf_chaselev_deque_hist_auth γ_hist (hist ++ [v]) pub) with "[> Hhist_auth]" as "Hhist_auth".
    { destruct pub as [| w pub]; first done.
      iMod (mono_list_auth_update_app with "Hhist_auth") as "($ & _)". done.
    }
    (* update state *)
    iAssert (inf_chaselev_deque_state γ_lock (S front1) back4 pub) with "[Hstate]" as "Hstate".
    { iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]".
      - iLeft. naive_solver auto with lia.
      - iRight. iFrame. iRight. iPureIntro.
        split; first lia. rewrite -length_zero_iff_nil. list_simplifier. lia.
      - naive_solver.
    }
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { iNext. iExists (S front1), back4, (hist ++ [v]), pub, priv. iFrame.
      iSplitL "Hfront".
      { replace (front1 + 1)%Z with (Z.of_nat (S front1)) by lia. done. }
      iSplitL "Hdata_model".
      { iApply (inf_array_model_proper with "Hdata_model").
        intros i. rewrite /= !app_length /=. destruct (decide _).
        - rewrite !decide_True; last lia. list_simplifier. done.
        - rewrite !decide_False; last lia. rewrite -assoc //.
      }
      iPureIntro. rewrite app_length /= //. lia.
    }
    clear- Hbr1.

    wp_pures.

    iApply "HΦ".
  Qed.

  Lemma inf_chaselev_deque_pop_spec t ι :
    <<<
      inf_chaselev_deque_inv t ι ∗ inf_chaselev_deque_owner t |
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
    iIntros "!> %Φ ((%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %data & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hdata & #Hinv) & (%_l & %_γ_ctl & %_γ_lock & %back & %priv & %Heq & #_Hmeta_ctl & #_Hmeta_lock & Hctl₂ & Hlock)) HΦ".
    injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_ctl _Hmeta_ctl") as %<-. iClear "_Hmeta_ctl".
    iDestruct (meta_agree with "Hmeta_lock _Hmeta_lock") as %<-. iClear "_Hmeta_lock".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front1 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front1.
    (* do load [back] *)
    wp_load.
    (* close invariant *)
    iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
    { repeat iExists _. iFrame. done. }
    clear.

    wp_pures.

    (* → [!#l.(data)] *)
    wp_load.

    wp_pures.

    (* → [#l.(back) <- #(back - 1)] *)
    wp_bind (#l.(back) <- #(back - 1))%E.
    (* open invariant *)
    iInv "Hinv" as "(%front2 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
    iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front2.
    (* do decrement [back] *)
    wp_store.
    (* update [back] in control tokens *)
    iMod (inf_chaselev_deque_ctl_update (back - 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
    (* we have lock, hence we are in state 1 *)
    iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %(Hstate & Hpub).
    (* branching 1 *)
    destruct (Z.lt_total back (front2 + 1)) as [Hbr1 | [-> | Hbr1]].

    (* branch 1.1: back = front2; empty deque *)
    - (* we are in state 1, hence [back = front2] *)
      assert (front2 = Z.to_nat back) as -> by lia.
      (* emit front fragment at [back] *)
      iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate Hlock".
      { iNext. iExists (Z.to_nat back), (back - 1)%Z, hist, pub, priv. iFrame. iSplit; first done.
        iRight. iFrame. iRight.
        iPureIntro. split; last rewrite -length_zero_iff_nil; lia.
      }
      clear.

      wp_pures.

      (* → [!#l.(front)] *)
      wp_bind (!#l.(front))%E.
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front3.
      (* do load [front] *)
      wp_load.
      (* from front fragment at [back], we know [back ≤ front3] *)
      iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront3.
      (* hence, we have [back = front3] *)
      iAssert ⌜back = front3⌝%I as %Hstate; last iEval (rewrite -Hstate).
      { iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; auto with lia. }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      clear.

      wp_pures.

      (* → [if: #(bool_decide (back - 1 < back))] *)
      rewrite bool_decide_eq_true_2; last lia.

      wp_pures.

      (* → [#l.(back) <- #back] *)
      wp_bind (#l.(back) <- #back)%E.
      (* open invariant *)
      iInv "Hinv" as "(%front4 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front4.
      (* do increment [back] *)
      wp_store.
      (* update [back] in control tokens *)
      iMod (inf_chaselev_deque_ctl_update back priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
      (* from front fragment at [back], we know [back ≤ front4] *)
      iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront4.
      (* hence, we are in state 2.2 *)
      iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; [lia.. |].
      (* hence, [front4 = back] *)
      assert (front4 = Z.to_nat back) as -> by lia.
      (* begin transaction *)
      iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-.
      iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
      (* end transaction *)
      iMod ("HΦ" $! NONEV with "[Hpub₂]") as "HΦ".
      { iLeft. simplify. iSplit; first done. repeat iExists _. naive_solver. }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁".
      { iNext. iExists (Z.to_nat back), back, hist, pub, priv. iFrame. iSplit; first done.
        iLeft. iPureIntro. naive_solver lia.
      }
      clear.

      wp_pures.

      iApply "HΦ". repeat iExists _. iFrame "∗#". done.

    (* branch 1.2: back = front2 + 1; race for last public value *)
    - assert ((front2 + 1 - 1)%Z = front2) as -> by lia.
      (* emit front fragment at [front2] *)
      iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      assert (∃ v, pub = [v]) as (v & ->).
      { assert (length pub = 1) by lia.
        destruct pub as [| v pub]; first done. eexists v. destruct pub; done.
      }
      (* emit history fragment at [front2] *)
      iAssert (inf_chaselev_deque_hist_frag γ_hist front2 v) as "#Hhist_frag".
      { iDestruct (mono_list_lb_get with "Hhist_auth") as "#Hhist_frag".
        iApply (mono_list_mapsto_get with "Hhist_frag").
        rewrite lookup_app_r; last lia.
        rewrite Hhist Nat.sub_diag //.
      }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate Hlock".
      { iNext. iExists front2, front2, hist, [v], priv. iFrame. iSplit; first done.
        iRight. iFrame. iLeft. iPureIntro. lia.
      }
      clear.

      wp_pures.

      (* → [!#l.(front)] *)
      wp_bind (!#l.(front))%E.
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front3.
      (* do load [front] *)
      wp_load.
      (* branching 2 *)
      iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]".

      (* branch 2.1: state 1; impossible *)
      + (* we have [front3 = front2] *)
        iAssert ⌜front3 = front2⌝%I as %->.
        { (* from front fragment at [front2], we know [front2 ≤ front3] *)
          iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
          iPureIntro. lia.
        }
        (* hence, [pub] is empty *)
        assert (pub = []) as ->.
        { apply length_zero_iff_nil. lia. }
        (* from history fragment at [front2], we know [hist !! front2 = Some v] *)
        iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hhist_lookup.
        (* absurd, as [length hist = front2] *)
        apply lookup_lt_Some in Hhist_lookup. lia.

      (* branch 2.2: state 2.1; [front] has not changed *)
      + destruct Hstate as (<-%(inj Z.of_nat) & Hpub).
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hlock".
        { iNext. iExists front2, front2, hist, pub, priv. iFrame. iSplit; first done.
          iRight. iFrame. iLeft. iPureIntro. lia.
        }
        clear.

        wp_pures.

        (* → [if: #(bool_decide (front2 < front2))] *)
        rewrite bool_decide_eq_false_2; last lia.

        wp_pures.

        (* → [array.(inf_array_get) data #front2] *)
        awp_apply (inf_array_get_spec with "[//]")  without "HΦ"; first lia.
        (* open invariant *)
        iInv "Hinv" as "(%front4 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & >Hdata_model & >%Hhist & >Hhist_auth & Hpub₁ & Hstate)".
        iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front4.
        iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
        { iModIntro. iFrame. iNext. repeat iExists _. iFrame. done. }
        (* from history fragment at [front2], we know [(hist ++ pub) !! front2 = Some v] *)
        iAssert ⌜(hist ++ pub) !! front2 = Some v⌝%I as %Hlookup.
        { iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hlookup.
          iPureIntro. destruct pub as [| w pub].
          - list_simplifier. done.
          - rewrite cons_middle assoc. apply lookup_app_l_Some. done.
        }
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
        { repeat iExists _. iFrame. done. }
        iIntros "_ HΦ".
        (* loaded value is [v] *)
        rewrite Nat2Z.id decide_True; last eauto using lookup_lt_Some.
        erewrite list_lookup_total_correct; last done.
        clear.

        wp_pures.

        (* → [if: #(bool_decide (front2 < front2))] *)
        rewrite bool_decide_eq_false_2; last lia.

        wp_pures.

        (* → [CmpXchg #l.(front) #front2 #(front2 + 1)] *)
        wp_bind (CmpXchg #l.(front) #front2 #(front2 + 1))%E.
        (* open invariant *)
        iInv "Hinv" as "(%front5 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & >Hfront_auth & Hdata_model & >%Hhist & >Hhist_auth & >Hpub₁ & >Hstate)".
        iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front5.
        (* branch 3 *)
        iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]".

        (* branch 3.1: state 1; impossible *)
        * (* we have [front5 = front2] *)
          iAssert ⌜front5 = front2⌝%I as %->.
          { (* from front fragment at [front2], we know [front2 ≤ front5] *)
            iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
            iPureIntro. lia.
          }
          (* hence, [pub] is empty *)
          assert (pub = []) as ->.
          { apply length_zero_iff_nil. lia. }
          (* from history fragment at [front2], we know [hist !! front2 = Some v] *)
          iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hhist_lookup.
          (* absurd, as [length hist = front2] *)
          apply lookup_lt_Some in Hhist_lookup. lia.

        (* branch 3.2: state 2.1; [front] has not changed *)
        * destruct Hstate as (<-%(inj Z.of_nat) & Hpub).
          (* from history fragment at [front2], we know [pub = [v]] *)
          iAssert ⌜pub = [v]⌝%I as %->.
          { destruct pub as [| w pub]; first done. destruct pub; last done.
            iDestruct (mono_list_auth_mapsto_lookup with "Hhist_auth Hhist_frag") as %Hlookup.
            rewrite lookup_app_r in Hlookup; last lia.
            rewrite list_lookup_singleton_Some in Hlookup.
            naive_solver.
          }
          (* begin transaction *)
          iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)".
          injection Heq as <-.
          iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
          iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
          (* do increment [front] *)
          wp_cmpxchg_suc.
          (* update front authority *)
          iMod (inf_chaselev_deque_front_auth_update (front2 + 1) with "Hfront_auth") as "Hfront_auth"; first lia.
          (* emit front fragment at [front3 + 1] *)
          iClear "Hfront_frag".
          iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
          (* update [pub] *)
          iMod (inf_chaselev_deque_pub_update [] with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
          (* end transaction *)
          iMod ("HΦ" with "[Hpub₂]") as "HΦ".
          { iRight. iExists [], v. iSplit; first done. repeat iExists _. naive_solver. }
          (* close invariant *)
          do 2 iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hlock".
          { iNext. iExists (front2 + 1), front2, (hist ++ [v]), [], priv. iFrame.
            iSplitL "Hfront".
            { assert (Z.of_nat (front2 + 1) = front2 + 1)%Z as -> by lia. done. }
            iSplitL "Hdata_model".
            { iApply (inf_array_model_proper with "Hdata_model").
              intros i. rewrite !app_length Nat.add_0_r /=.
              destruct (decide _); list_simplifier; done.
            }
            iSplit; first solve_length.
            iRight. iFrame. iRight. iPureIntro. naive_solver lia.
          }
          clear.

          wp_pures.

          (* → [#l.(back) <- #(front2 + 1)] *)
          wp_bind (#l.(back) <- #(front2 + 1))%E.
          (* open invariant *)
          iInv "Hinv" as "(%front6 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
          iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front6.
          (* do increment [back] *)
          wp_store.
          (* update [back] in control tokens *)
          iMod (inf_chaselev_deque_ctl_update (front2 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
          (* from front fragment at [front2 + 1], we know [front2 + 1 ≤ front6] *)
          iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront6.
          (* hence, we are in state 2.2 *)
          iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; [lia.. |].
          (* hence, [front6 = front2 + 1] *)
          assert (front6 = front2 + 1) as -> by lia.
          (* close invariant *)
          iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁".
          { iNext. iExists (front2 + 1), (front2 + 1)%Z, hist, pub, priv. iFrame. iSplit; first done.
            iLeft. iPureIntro. naive_solver lia.
          }
          clear.

          wp_pures.

          iApply "HΦ". repeat iExists _. iFrame "∗#". done.

        (* branch 3.3: state 2.2; [front] has changed: last element was stolen *)
        * destruct Hstate as (Hstate & ->). assert (front5 = front2 + 1) as -> by lia.
          (* do not increment [front] *)
          wp_cmpxchg_fail; first naive_solver lia.
          (* emit front fragment at [front2 + 1] *)
          iClear "Hfront_frag".
          iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
          (* close invariant *)
          iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hlock".
          { iNext. iExists (front2 + 1), front2, hist, [], priv. iFrame. iSplit; first done.
            iRight. iFrame. iRight. done.
          }
          clear.

          wp_pures.

          (* → [#l.(back) <- #(front2 + 1)] *)
          wp_bind (#l.(back) <- #(front2 + 1))%E.
          (* open invariant *)
          iInv "Hinv" as "(%front6 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
          iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front6.
          (* do increment [back] *)
          wp_store.
          (* update [back] in control tokens *)
          iMod (inf_chaselev_deque_ctl_update (front2 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
          (* from front fragment at [front 2 + 1], we know [front2 + 1 ≤ front6] *)
          iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront6.
          (* hence, we are in state 2.2 *)
          iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; [lia.. |].
          (* hence, [front6 = front2 + 1] *)
          assert (front6 = front2 + 1) as -> by lia.
          (* begin transaction *)
          iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-.
          iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
          (* end transaction *)
          iMod ("HΦ" $! NONEV with "[Hpub₂]") as "HΦ".
          { iLeft. simplify. iSplit; first done. repeat iExists _. naive_solver. }
          (* close invariant *)
          iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁".
          { iNext. iExists (front2 + 1), (front2 + 1)%Z, hist, pub, priv. iFrame. iSplit; first done.
            iLeft. iPureIntro. naive_solver lia.
          }
          clear.

          wp_pures.

          iApply "HΦ". repeat iExists _. iFrame "∗#". done.

      (* branch 2.3: state 2.2; [front] has changed: last element was stolen *)
      + destruct Hstate as (Hstate & ->). assert (front3 = front2 + 1) as -> by lia.
        (* emit front fragment at [front2 + 1] *)
        iClear "Hfront_frag".
        iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hlock".
        { iNext. iExists (front2 + 1), front2, hist, [], priv. iFrame. iSplit; first done.
          iRight. iFrame. iRight. done.
        }
        clear.

        wp_pures.

        (* → [if: #(bool_decide (front2 < front2 + 1))] *)
        rewrite bool_decide_eq_true_2; last lia.

        wp_pures.

        (* → [#l.(back) <- #(front2 + 1)] *)
        wp_bind (#l.(back) <- #(front2 + 1)%nat)%E.
        (* open invariant *)
        iInv "Hinv" as "(%front4 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
        iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front4.
        (* do increment [back] *)
        wp_store.
        (* update [back] in control tokens *)
        iMod (inf_chaselev_deque_ctl_update (front2 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
        (* from front fragment at [front2 + 1], we know [front2 + 1 ≤ front4] *)
        iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront4.
        (* hence, we are in state 2.2 *)
        iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; [lia.. |].
        (* hence, [front4 = front2 + 1] *)
        assert (front4 = front2 + 1) as -> by lia.
        (* begin transaction *)
        iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-.
        iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
        (* end transaction *)
        iMod ("HΦ" $! NONEV with "[Hpub₂]") as "HΦ".
        { iLeft. simplify. iSplit; first done. repeat iExists _. naive_solver. }
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁".
        { iNext. iExists (front2 + 1), (front2 + 1)%Z, hist, pub, priv. iFrame.
          iSplitL "Hback".
          { assert (Z.of_nat (front2 + 1) = front2 + 1)%Z as -> by lia. done. }
          iSplit; first done.
          iLeft. iPureIntro. naive_solver lia.
        }
        clear.

        wp_pures.

        iApply "HΦ". repeat iExists _. iFrame "∗#". done.

    (* branch 1.3: front2 + 1 < back; no conflict *)
    - (* we are in state 1, hence there is more than one public value *)
      assert (∃ pub' v, pub = pub' ++ [v] ∧ length pub' = Z.to_nat (back - front2 - 1)) as (pub' & v & -> & Hpub').
      {
        assert (∃ rev_pub' v, reverse pub = v :: rev_pub' ∧ length rev_pub' = Z.to_nat (back - front2 - 1)) as (rev_pub' & v & Hrev_pub & Hrev_pub').
        { rewrite -reverse_length in Hpub.
          destruct (reverse pub) as [| v rev_pub']; naive_solver lia.
        }
        exists (reverse rev_pub'), v. split.
        - apply (inj reverse). rewrite reverse_snoc reverse_involutive //.
        - rewrite reverse_length //.
      }
      (* update [priv] in control tokens *)
      set (priv' := λ i, if decide (i = 0) then v else priv (i - 1)).
      iMod (inf_chaselev_deque_ctl_update (back - 1) priv' with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
      (* begin transaction *)
      iMod "HΦ" as "(%_pub & (%_l & %_γ_pub & %Heq & #_Hmeta_pub & Hpub₂) & (_ & HΦ))". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta_pub _Hmeta_pub") as %<-. iClear "_Hmeta_pub".
      iDestruct (inf_chaselev_deque_pub_agree with "Hpub₁ Hpub₂") as %<-.
      (* update [pub] *)
      iMod (inf_chaselev_deque_pub_update pub' with "Hpub₁ Hpub₂") as "(Hpub₁ & Hpub₂)".
      (* end transaction *)
      iMod ("HΦ" with "[Hpub₂]") as "HΦ".
      { iRight. iExists pub', v. iSplit; first done. repeat iExists _. naive_solver. }
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { iNext. iExists front2, (back - 1)%Z, hist, pub', priv'. iFrame.
        (* data remain unchanged *)
        iSplitL "Hdata_model".
        { iApply (inf_array_model_proper with "Hdata_model").
          intros i. rewrite !app_length Hhist /=. rewrite app_length /= in Hpub.
          destruct (Nat.lt_total i (Z.to_nat (back - 1))) as [| [-> |]].
          - rewrite !decide_True; [| naive_solver lia..].
            rewrite assoc (lookup_total_app_l _ [v]); first done.
            rewrite app_length. lia.
          - rewrite decide_False; last lia.
            rewrite decide_True; last lia.
            rewrite assoc lookup_total_app_r; last (rewrite app_length; lia).
            rewrite app_length Hhist.
            assert (Z.to_nat (back - 1) - (front2 + length pub') = 0) as -> by lia.
            done.
          - rewrite !decide_False; [| lia..].
            rewrite /priv' decide_False; last lia.
            f_equal. lia.
        }
        iSplit; first done.
        (* [hist] remains unchanged *)
        iSplitL "Hhist_auth".
        { destruct pub' as [| v' pub'']; [naive_solver lia | done]. }
        (* update state *)
        iLeft. iPureIntro. lia.
      }
      clear.

      wp_pures.

      (* → [!#l.(front)] *)
      wp_bind (!#l.(front))%E.
      (* open invariant *)
      iInv "Hinv" as "(%front3 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
      iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front3.
      (* do load [front] *)
      wp_load.
      (* we have lock, hence we are in state 1, hence [front3 ≤ back - 1] *)
      iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %(Hfront3 & _).
      (* emit front fragment at [front3] (to be used in branch 2.2) *)
      iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      clear- Hfront3.

      wp_pures.

      (* → [if: #(bool_decide (back - 1 < front3))] *)
      rewrite bool_decide_eq_false_2; last lia.

      wp_pures.

      (* → [array.(inf_array_get) data #(back - 1)] *)
      awp_apply (inf_array_get_spec with "[//]") without "HΦ"; first lia.
      (* open invariant *)
      iInv "Hinv" as "(%front4 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & >Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & >Hstate)".
      iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front4.
      iAaccIntro with "Hdata_model"; iIntros "Hdata_model".
      { iModIntro. iFrame. iNext. repeat iExists _. iFrame. done. }
      (* we have lock, hence we are in state 1 *)
      iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %Hstate.
      (* close invariant *)
      iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate".
      { repeat iExists _. iFrame. done. }
      iIntros "_ HΦ".
      (* loaded value is [v] *)
      rewrite app_length decide_False; last lia.
      assert (Z.to_nat (back - 1) - (length hist + length pub) = 0) as -> by lia.
      iEval (rewrite /priv' /=).
      clear- Hfront3.

      wp_pures.

      (* branching 2 *)
      rewrite Z.le_lteq in Hfront3. destruct Hfront3 as [Hfront3 | Hfront3].

      (* branch 2.1: [front3 < back - 1] *)
      + (* → [if: #(bool_decide (back - 1 < front3))] *)
        rewrite bool_decide_eq_true_2; last lia.

        wp_pures.

        iApply "HΦ". repeat iExists _. iFrame "∗#". done.

      (* branch 2.2: [back = front3 + 1] *)
      + assert (back = front3 + 1) as -> by lia.
        assert ((front3 + 1)%nat - 1 = front3)%Z as -> by lia.

        (* → [if: #(bool_decide (front3 < front3))] *)
        rewrite bool_decide_eq_false_2; last lia.

        wp_pures.

        (* → [CmpXchg #l.(front) #front3 #(front3 + 1)] *)
        wp_bind (CmpXchg #l.(front) #front3 #(front3 + 1))%E.
        (* open invariant *)
        iInv "Hinv" as "(%front5 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & >Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & >Hstate)".
        iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front5.
        (* we have [front5 = front3] *)
        iAssert ⌜front5 = front3⌝%I as %->.
        { (* we have lock, hence we are in state 1 *)
          iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %?.
          (* from front fragment at [front3], we know [front3 ≤ front5] *)
          iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %?.
          iPureIntro. lia.
        }
        (* CAS must succeed *)
        wp_cmpxchg_suc.
        (* update front authority *)
        iMod (inf_chaselev_deque_front_auth_update (front3 + 1) with "Hfront_auth") as "Hfront_auth"; first lia.
        (* emit front fragment at [front3 + 1] *)
        iClear "Hfront_frag".
        iDestruct (inf_chaselev_deque_front_frag_get with "Hfront_auth") as "#Hfront_frag".
        (* we have lock, hence we are in state 1 *)
        iDestruct (inf_chaselev_deque_lock_state with "Hlock Hstate") as %(_ & Hpub).
        (* hence, [pub] is empty *)
        assert (length pub = 0) as ->%length_zero_iff_nil by lia. clear Hpub.
        (* update [hist] *)
        set (hist' := hist ++ [v]).
        iAssert (inf_chaselev_deque_hist_auth γ_hist hist' []) with "[> Hhist_auth]" as "Hhist_auth".
        { iMod (mono_list_auth_update_app with "Hhist_auth") as "($ & _)". done. }
        (* update [priv] in control tokens *)
        iMod (inf_chaselev_deque_ctl_update front3 priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁ Hstate Hlock".
        { iNext. iExists (front3 + 1), front3, hist', [], priv. iFrame.
          iSplitL "Hfront".
          { assert (Z.of_nat (front3 + 1) = front3 + 1)%Z as -> by lia. done. }
          iSplitL "Hdata_model".
          { iApply (inf_array_model_proper with "Hdata_model").
            intros i. rewrite !app_length !app_nil_r !Nat.add_0_r Hhist /=.
            destruct (Nat.lt_total i front3) as [| [-> |]].
            - rewrite !decide_True; [| lia..].
              rewrite lookup_total_app_l; naive_solver.
            - rewrite decide_True; last lia.
              rewrite decide_False; last lia.
              rewrite lookup_total_app_r; last lia.
              rewrite Hhist Nat.sub_diag //.
            - rewrite !decide_False; [| lia..].
              rewrite /priv' decide_False; last lia.
              f_equal. lia.
          }
          iSplit.
          { iPureIntro. rewrite app_length /=. lia. }
          iRight. iFrame. iRight. auto with lia.
        }
        clear.

        wp_pures.

        (* → [#l.(back) <- #(front3 + 1)] *)
        wp_bind (#l.(back) <- #(front3 + 1))%E.
        (* open invariant *)
        iInv "Hinv" as "(%front6 & %_back & %hist & %pub & %_priv & Hfront & Hback & >Hctl₁ & Hfront_auth & Hdata_model & >%Hhist & Hhist_auth & Hpub₁ & Hstate)".
        iDestruct (inf_chaselev_deque_ctl_agree with "Hctl₁ Hctl₂") as %?. simplify- front6.
        (* do increment [back] *)
        wp_store.
        (* update [back] in control tokens *)
        iMod (inf_chaselev_deque_ctl_update (front3 + 1) priv with "Hctl₁ Hctl₂") as "(Hctl₁ & Hctl₂)".
        (* from front fragment at [front3 + 1], we know [front3 + 1 ≤ front6] *)
        iDestruct (inf_chaselev_deque_front_valid with "Hfront_auth Hfront_frag") as %Hfront6.
        (* hence, we are in state 2.2 *)
        iDestruct "Hstate" as "[%Hstate | (Hlock & [%Hstate | %Hstate])]"; [lia.. |].
        (* hence, [front6 = front3 + 1] *)
        assert (front6 = front3 + 1) as -> by lia.
        (* close invariant *)
        iModIntro. iSplitL "Hfront Hback Hctl₁ Hfront_auth Hdata_model Hhist_auth Hpub₁".
        { iNext. iExists (front3 + 1), (front3 + 1)%Z, hist, pub, priv. iFrame. iSplit; first done.
          iLeft. iPureIntro. naive_solver lia.
        }
        clear.

        wp_pures.

        iApply "HΦ". repeat iExists _. iFrame "∗#". done.
  Qed.

  Lemma inf_chaselev_deque_unboxed t ι :
    inf_chaselev_deque_inv t ι -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ_ctl & %γ_front & %γ_hist & %γ_pub & %γ_lock & %data & -> & #Hmeta_ctl & #Hmeta_front & #Hmeta_hist & #Hmeta_pub & #Hmeta_lock & #Hdata & #Hinv) //".
  Qed.
End inf_chaselev_deque_G.

#[global] Opaque inf_chaselev_deque_make.
#[global] Opaque inf_chaselev_deque_push.
#[global] Opaque inf_chaselev_deque_steal.
#[global] Opaque inf_chaselev_deque_pop.

#[global] Opaque inf_chaselev_deque_inv.
#[global] Opaque inf_chaselev_deque_model.
#[global] Opaque inf_chaselev_deque_owner.
