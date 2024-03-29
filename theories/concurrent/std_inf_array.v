From Coq.Logic Require Import
  FunctionalExtensionality.

From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  record3
  array.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mutex
  inf_array.

Class StdInfArrayGpre Σ `{!heapGS Σ} := {
  #[local] std_inf_array_Gpre_model_G :: AuthExclG Σ (nat -d> valO) ;
}.

Class StdInfArrayG Σ `{!heapGS Σ} := {
  #[local] std_inf_array_G_Gpre :: StdInfArrayGpre Σ ;
  std_inf_array_G_mutex : mutex Σ false ;
}.

Definition std_inf_array_Σ := #[
  auth_excl_Σ (nat -d> valO)
].
#[global] Instance subG_std_inf_array_Σ Σ `{!heapGS Σ} :
  subG std_inf_array_Σ Σ →
  StdInfArrayGpre Σ.
Proof.
  solve_inG.
Qed.

Section std_inf_array_G.
  Context `{std_inf_array_G : StdInfArrayG Σ}.
  Implicit Types l : loc.
  Implicit Types v t : val.
  Implicit Types us : list val.
  Implicit Types vs : nat → val.

  Let mutex := std_inf_array_G.(std_inf_array_G_mutex).

  Notation "t '.(data)'" := t.(0)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(default)'" := t.(1)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(mutex)'" := t.(2)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(data)'" := t.(0)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(default)'" := t.(1)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(mutex)'" := t.(2)%E
  ( at level 5
  ) : expr_scope.

  Definition std_inf_array_make : val :=
    λ: "default",
      let: "data" := array_make #0 "default" in
      let: "t" := record3_make "data" "default" #() in
      let: "mtx" := mutex.(mutex_make) #() in
      "t".(mutex) <- "mtx" ;;
      "t".

  Definition std_inf_array_get : val :=
    λ: "t" "i",
      mutex.(mutex_protect) !"t".(mutex) (λ: <>,
        let: "data" := !"t".(data) in
        if: "i" < array_size "data" then (
          array_get "data" "i"
        ) else (
          !"t".(default)
        )
      ).

  Definition std_inf_array_set : val :=
    λ: "t" "i" "v",
      mutex.(mutex_protect) !"t".(mutex) (λ: <>,
        let: "data" := !"t".(data) in
        let: "sz" := array_size "data" in
        if: "i" < "sz" then (
          array_set "data" "i" "v"
        ) else (
          let: "data" := array_grow "data" ("i" + #1) !"t".(default) in
          "t".(data) <- "data" ;;
          array_set "data" "i" "v"
        )
      ).

  #[local] Definition std_inf_array_inv_inner l γ default : iProp Σ :=
    ∃ data us vs,
    l.(data) ↦ data ∗
    array_model data (DfracOwn 1) us ∗
    auth_excl_frag γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else default⌝.
  Definition std_inf_array_inv t : iProp Σ :=
    ∃ l γ default mtx,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.(mutex) ↦□ mtx ∗
    l.(default) ↦□ default ∗
    mutex.(mutex_inv) mtx (std_inf_array_inv_inner l γ default).

  Definition std_inf_array_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    auth_excl_auth γ (DfracOwn 1) vs.

  #[global] Instance std_inf_array_inv_persistent t :
    Persistent (std_inf_array_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance std_inf_array_model_timeless t vs :
    Timeless (std_inf_array_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_inf_array_make_spec default :
    {{{ True }}}
      std_inf_array_make default
    {{{ t,
      RET t;
      std_inf_array_inv t ∗
      std_inf_array_model t (λ _, default)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_apply (array_make_spec with "[//]"); first done. iIntros "%data Hmodel_data".

    wp_smart_apply (record3_make_spec with "[//]"). iIntros "%l (Hl & Hmeta)".
    iDestruct (record3_model_eq_1 with "Hl") as "(Hdata & Hdefault & Hmtx)".
    iMod (mapsto_persist with "Hdefault") as "#Hdefault".

    set (vs _ := default).
    iMod (auth_excl_alloc' (auth_excl_G := std_inf_array_Gpre_model_G) vs) as "(%γ & Hmodel₁ & Hmodel₂)".
    iMod (meta_set _ _ γ nroot with "Hmeta") as "#Hmeta"; first done.

    wp_smart_apply (mutex_make_spec _ (std_inf_array_inv_inner l γ default) with "[Hdata Hmodel_data Hmodel₂]").
    { iExists data, [], vs. iFrame. iPureIntro.
      apply functional_extensionality => i. case_decide; naive_solver lia.
    }
    iIntros "%mtx #Hinv_mtx".

    wp_store.

    iMod (mapsto_persist with "Hmtx") as "#Hmtx".

    iApply "HΦ". iSplitR.
    - iExists l, γ, default, mtx. iFrame "#∗". done.
    - iExists l, γ. auto.
  Qed.

  Lemma std_inf_array_get_spec t i :
    (0 ≤ i)%Z →
    <<<
      std_inf_array_inv t
    | ∀∀ vs, std_inf_array_model t vs
    >>>
      std_inf_array_get t #i
    <<<
      std_inf_array_model t vs
    | RET vs (Z.to_nat i); True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %default & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    rename i into _i. destruct (Z_of_nat_complete _i) as (i & ->); first lia.
    rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec' with "Hmodel_data"). iIntros "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; last lia.

      iApply wp_fupd.
      wp_smart_apply (array_get_spec with "Hmodel_data"); first done.
      { rewrite Nat2Z.id list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first (iExists l, γ; auto).

      iIntros "Hmodel_data !>". iFrame. iSplitR "HΦ".
      { iExists data, us, vs. auto with iFrame. }
      rewrite Hvs decide_True; last lia.
      iApply ("HΦ" with "[//]").

    - rewrite bool_decide_eq_false_2; last lia. wp_load.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first (iExists l, γ; auto).

      iModIntro. iFrame. iSplitR "HΦ".
      { iExists data, us, vs. auto with iFrame. }
      rewrite Hvs decide_False; last lia.
      iApply ("HΦ" with "[//]").
  Qed.

  Lemma std_inf_array_set_spec t i v :
    (0 ≤ i)%Z →
    <<<
      std_inf_array_inv t
    | ∀∀ vs, std_inf_array_model t vs
    >>>
      std_inf_array_set t #i v
    <<<
      std_inf_array_model t (<[Z.to_nat i := v]> vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %default & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    rename i into _i. destruct (Z_of_nat_complete _i) as (i & ->); first lia.
    rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec' with "Hmodel_data"). iIntros "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; last lia.

      iApply wp_fupd.
      wp_smart_apply (array_set_spec with "Hmodel_data"); first done.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      set us' := <[i := v]> us.
      set vs' := <[i := v]> vs.
      iMod (auth_excl_update' (auth_excl_G := std_inf_array_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
      { iExists l, γ. auto. }

      iIntros "Hmodel_data !>". iFrame. iSplitR "HΦ".
      { iExists data, us', vs'. rewrite Nat2Z.id. iFrame. iPureIntro.
        rewrite /us' /vs' insert_length Hvs.
        apply functional_extensionality => j. destruct (decide (j = i)) as [-> |].
        - rewrite fn_lookup_insert decide_True; last lia.
          rewrite list_lookup_total_insert //. lia.
        - rewrite fn_lookup_insert_ne //. case_decide; last done.
          rewrite list_lookup_total_insert_ne //.
      }
      iApply ("HΦ" with "[//]").

    - rewrite bool_decide_eq_false_2; last lia. wp_load.

      wp_smart_apply (array_grow_spec with "Hmodel_data"); first lia. iIntros "%data' (_ & Hmodel_data')".
      rewrite Z.add_1_r -Nat2Z.inj_succ Nat2Z.id.

      wp_store.

      iApply wp_fupd.
      wp_apply (array_set_spec with "Hmodel_data'").
      { rewrite app_length replicate_length. lia. }
      rewrite Nat2Z.id insert_app_r_alt; last lia.
      rewrite insert_replicate_lt; last lia.
      rewrite -Nat.sub_succ_l; last lia.
      rewrite Nat.sub_diag /=.
      iIntros "Hmodel_data'".

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
      set us' := us ++ replicate (i - length us) default ++ [v].
      set vs' := <[i := v]> vs.
      iMod (auth_excl_update' (auth_excl_G := std_inf_array_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
      { iExists l, γ. auto. }

      iModIntro. iFrame. iSplitR "HΦ".
      { iExists data', us', vs'. iFrame. iPureIntro.
        rewrite /us' /vs' !app_length replicate_length Hvs /=.
        apply functional_extensionality => j. destruct (Nat.lt_total j i) as [| [-> |]].
        - rewrite fn_lookup_insert_ne; last lia.
          rewrite (@decide_True _ (j < _ + _)); last lia.
          case_decide.
          + rewrite lookup_total_app_l //.
          + rewrite lookup_total_app_r; last lia.
            rewrite lookup_total_app_l; last (rewrite replicate_length //; lia).
            rewrite lookup_total_replicate_2 //. lia.
        - rewrite fn_lookup_insert decide_True; last lia.
          rewrite lookup_total_app_r; last lia.
          rewrite lookup_total_app_r; last (rewrite replicate_length; lia).
          rewrite replicate_length Nat.sub_diag //.
        - rewrite fn_lookup_insert_ne; last lia.
          rewrite !decide_False //; lia.
      }
      iApply ("HΦ" with "[//]").
  Qed.

  Lemma std_inf_array_unboxed t :
    std_inf_array_inv t -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ & %default & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) //".
  Qed.

  Program Definition std_inf_array : inf_array Σ true := {|
    inf_array_make :=
      std_inf_array_make ;
    inf_array_get :=
      std_inf_array_get ;
    inf_array_set :=
      std_inf_array_set ;

    inf_array_name :=
      unit ;
    inf_array_inv t _ _ :=
      std_inf_array_inv t ;
    inf_array_model t _ vs :=
      std_inf_array_model t vs ;
  |}.
  Next Obligation.
    iIntros "* _ HΦ".
    wp_apply (std_inf_array_make_spec with "[//]"). iIntros "%t (#Hinv & Hmodel)".
    iApply ("HΦ" $! t ()). auto.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using std_inf_array_get_spec.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using std_inf_array_set_spec.
  Qed.
  Next Obligation.
    simpl. eauto using std_inf_array_unboxed.
  Qed.
End std_inf_array_G.

#[global] Opaque std_inf_array_make.
#[global] Opaque std_inf_array_get.
#[global] Opaque std_inf_array_set.

#[global] Opaque std_inf_array_inv.
#[global] Opaque std_inf_array_model.
