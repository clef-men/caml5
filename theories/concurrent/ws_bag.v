From iris.algebra Require Import
  list.

From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  spmc_stack
  spmc_queue
  ws_deque.

Implicit Types v t : val.

Record ws_bag `{!heapGS Σ} := {
  ws_bag_make : val ;
  ws_bag_push : val ;
  ws_bag_pop : val ;
  ws_bag_steal : val ;

  ws_bag_name : Type ;
  ws_bag_inv : val → ws_bag_name → namespace → (val → iProp Σ) → iProp Σ ;
  ws_bag_model : val → ws_bag_name → nat → iProp Σ ;
  ws_bag_owner : val → ws_bag_name → iProp Σ ;

  ws_bag_inv_ne t γ ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bag_inv t γ ι) ;
  ws_bag_inv_persistent t γ ι Ψ :
    Persistent (ws_bag_inv t γ ι Ψ) ;
  ws_bag_model_timeless t γ sz :
    Timeless (ws_bag_model t γ sz) ;
  ws_bag_owner_timeless t γ :
    Timeless (ws_bag_owner t γ) ;

  ws_bag_owner_exclusive t γ :
    ws_bag_owner t γ -∗
    ws_bag_owner t γ -∗
    False ;

  ws_bag_make_spec ι Ψ :
    {{{ True }}}
      ws_bag_make #()
    {{{ t γ,
      RET t;
      ws_bag_inv t γ ι Ψ ∗
      ws_bag_model t γ 0 ∗
      ws_bag_owner t γ
    }}} ;

  ws_bag_push_spec t γ ι Ψ v :
    <<<
      ws_bag_inv t γ ι Ψ ∗
      ws_bag_owner t γ ∗ Ψ v |
      ∀∀ sz, ws_bag_model t γ sz
    >>>
      ws_bag_push t v
      @ ↑ ι
    <<<
      ws_bag_model t γ (S sz) |
      RET #(); ws_bag_owner t γ
    >>> ;

  ws_bag_pop_spec t γ ι Ψ :
    <<<
      ws_bag_inv t γ ι Ψ ∗
      ws_bag_owner t γ |
      ∀∀ sz, ws_bag_model t γ sz
    >>>
      ws_bag_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      ws_bag_owner t γ ∗
      from_option Ψ True o
    >>> ;

  ws_bag_steal_spec t γ ι Ψ :
    <<<
      ws_bag_inv t γ ι Ψ |
      ∀∀ sz, ws_bag_model t γ sz
    >>>
      ws_bag_steal t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>> ;
}.
#[global] Arguments ws_bag _ {_} : assert.
#[global] Arguments Build_ws_bag {_ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Existing Instance ws_bag_inv_ne.
#[global] Existing Instance ws_bag_inv_persistent.
#[global] Existing Instance ws_bag_model_timeless.
#[global] Existing Instance ws_bag_owner_timeless.

#[global] Instance ws_bag_inv_proper `{!heapGS Σ} ws_bag t γ ι :
  Proper (pointwise_relation val (≡) ==> (≡)) (ws_bag.(ws_bag_inv) t γ ι).
Proof.
  intros Ψ1 Ψ2 HΨ.
  rewrite /pointwise_relation in HΨ. setoid_rewrite equiv_dist in HΨ.
  rewrite equiv_dist. intros n. f_equiv. intros v. done.
Qed.

Class WsBagOfWsDequeG Σ `{!heapGS Σ} := {
  ws_bag_of_ws_deque_G_ctl_G : AuthExclG Σ (listO valO) ;
}.
#[local] Existing Instance ws_bag_of_ws_deque_G_ctl_G.

Definition ws_bag_of_ws_deque_Σ := #[
  auth_excl_Σ (listO valO)
].
Lemma subG_ws_bag_of_ws_deque_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_ws_deque_Σ Σ →
  WsBagOfWsDequeG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_ws_deque.
  Context `{WsBagOfWsDequeG Σ} (ws_deque : ws_deque Σ).
  Implicit Types γ : ws_deque.(ws_deque_name) * gname.

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_ws_deque_meta_ctl := (nroot .@ "ctl").

  Notation ws_bag_of_ws_deque_namespace_base ι := (ι .@ "base").
  Notation ws_bag_of_ws_deque_namespace_extra ι := (ι .@ "extra").

  #[local] Definition ws_bag_of_ws_deque_make :=
    ws_deque.(ws_deque_make).

  #[local] Definition ws_bag_of_ws_deque_push :=
    ws_deque.(ws_deque_push).

  #[local] Definition ws_bag_of_ws_deque_pop : val :=
    λ: "t",
      let: "o" := ws_deque.(ws_deque_pop) "t" in
      "o".

  #[local] Definition ws_bag_of_ws_deque_steal : val :=
    λ: "t",
      let: "o" := ws_deque.(ws_deque_steal) "t" in
      "o".

  #[local] Definition ws_bag_of_ws_deque_ctl₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_ws_deque_ctl₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_ws_deque_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_ws_deque_ctl₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_ws_deque_inv t γ ι Ψ : iProp Σ :=
    ws_deque.(ws_deque_inv) t γ.(base) (ws_bag_of_ws_deque_namespace_base ι) ∗
    inv (ws_bag_of_ws_deque_namespace_extra ι) (ws_bag_of_ws_deque_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_ws_deque_model t γ sz : iProp Σ :=
    ∃ vs,
    ⌜sz = length vs⌝ ∗
    ws_bag_of_ws_deque_ctl₂ γ vs ∗
    ws_deque.(ws_deque_model) t γ.(base) vs.

  #[local] Definition ws_bag_of_ws_deque_owner t γ :=
    ws_deque.(ws_deque_owner) t γ.(base).

  #[local] Instance ws_bag_of_ws_deque_inv_contractive t γ ι n :
    Proper (pointwise_relation val (dist_later n) ==> (≡{n}≡)) (ws_bag_of_ws_deque_inv t γ ι).
  Proof.
    rewrite /ws_bag_of_ws_deque_inv /ws_bag_of_ws_deque_inv_inner. solve_contractive.
  Qed.
  #[local] Instance ws_bag_of_ws_deque_inv_ne t γ ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bag_of_ws_deque_inv t γ ι).
  Proof.
    intros Ψ1 Ψ2 HΨ. f_equiv. intros v. apply dist_dist_later. done.
  Qed.
  #[local] Instance ws_bag_of_ws_deque_inv_persistent t γ ι Ψ :
    Persistent (ws_bag_of_ws_deque_inv t γ ι Ψ).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_ws_deque_model_timeless t γ sz :
    Timeless (ws_bag_of_ws_deque_model t γ sz).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_ws_deque_owner_timeless t γ :
    Timeless (ws_bag_of_ws_deque_owner t γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_owner_exclusive t γ :
    ws_bag_of_ws_deque_owner t γ -∗
    ws_bag_of_ws_deque_owner t γ -∗
    False.
  Proof.
    apply ws_deque_owner_exclusive.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_make_spec ι Ψ :
    {{{ True }}}
      ws_bag_of_ws_deque_make #()
    {{{ t γ,
      RET t;
      ws_bag_of_ws_deque_inv t γ ι Ψ ∗
      ws_bag_of_ws_deque_model t γ 0 ∗
      ws_bag_of_ws_deque_owner t γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (ws_deque_make_spec with "[//]"). iIntros "%t %γ_base (#Hinv_deque & Hmodel_deque & Howner)".
    iMod (auth_excl_alloc' []) as "(%γ_extra & Hctl₂ & Hctl₁)".
    iApply ("HΦ" $! t (γ_base, γ_extra)). iFrame. iSplitL "Hctl₁".
    - iFrame "#". iApply inv_alloc. iNext. iExists []. iFrame. done.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ ∗
      ws_bag_of_ws_deque_owner t γ ∗
      Ψ v |
      ∀∀ sz, ws_bag_of_ws_deque_model t γ sz
    >>>
      ws_bag_of_ws_deque_push t v
      @ ↑ ι
    <<<
      ws_bag_of_ws_deque_model t γ (S sz) |
      RET #(); ws_bag_of_ws_deque_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner & Hv) HΦ".
    awp_apply (ws_deque_push_spec with "[$Hinv_deque $Howner]").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := vs ++ [v].
      iIntros "Hmodel_deque".
      iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
      iModIntro. iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs'. rewrite app_length /=. auto with iFrame lia. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ ∗
      ws_bag_of_ws_deque_owner t γ |
      ∀∀ sz, ws_bag_of_ws_deque_model t γ sz
    >>>
      ws_bag_of_ws_deque_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_ws_deque_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_ws_deque_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      ws_bag_of_ws_deque_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner) HΦ".
    wp_rec.
    awp_apply (ws_deque_pop_spec with "[$Hinv_deque $Howner]").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%vs' & %v & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit.
          { rewrite app_length (comm Nat.add) //. }
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ |
      ∀∀ sz, ws_bag_of_ws_deque_model t γ sz
    >>>
      ws_bag_of_ws_deque_steal t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_ws_deque_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_ws_deque_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hinv_deque & #Hinv_extra) HΦ".
    wp_rec.
    awp_apply (ws_deque_steal_spec with "Hinv_deque").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%v & %vs' & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit; first done.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  Definition ws_bag_of_ws_deque :=
    Build_ws_bag
      ws_bag_of_ws_deque_owner_exclusive
      ws_bag_of_ws_deque_make_spec
      ws_bag_of_ws_deque_push_spec
      ws_bag_of_ws_deque_pop_spec
      ws_bag_of_ws_deque_steal_spec.
End ws_bag_of_ws_deque.

Class WsBagOfSpmcStackG Σ `{!heapGS Σ} := {
  ws_bag_of_spmc_stack_G_ctl_G : AuthExclG Σ (listO valO) ;
}.
#[local] Existing Instance ws_bag_of_spmc_stack_G_ctl_G.

Definition ws_bag_of_spmc_stack_Σ := #[
  auth_excl_Σ (listO valO)
].
Lemma subG_ws_bag_of_spmc_stack_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_spmc_stack_Σ Σ →
  WsBagOfSpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_spmc_stack.
  Context `{WsBagOfSpmcStackG Σ} (spmc_stack : spmc_stack Σ).
  Implicit Types γ : spmc_stack.(spmc_stack_name) * gname.

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_spmc_stack_meta_ctl := (nroot .@ "ctl").

  Notation ws_bag_of_spmc_stack_namespace_base ι := (ι .@ "base").
  Notation ws_bag_of_spmc_stack_namespace_extra ι := (ι .@ "extra").

  #[local] Definition ws_bag_of_spmc_stack_make :=
    spmc_stack.(spmc_stack_make).

  #[local] Definition ws_bag_of_spmc_stack_push :=
    spmc_stack.(spmc_stack_push).

  #[local] Definition ws_bag_of_spmc_stack_pop : val :=
    λ: "t",
      let: "o" := spmc_stack.(spmc_stack_pop) "t" in
      "o".

  #[local] Definition ws_bag_of_spmc_stack_steal : val :=
    λ: "t",
      let: "o" := spmc_stack.(spmc_stack_pop) "t" in
      "o".

  #[local] Definition ws_bag_of_spmc_stack_ctl₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_spmc_stack_ctl₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_spmc_stack_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_spmc_stack_ctl₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_spmc_stack_inv t γ ι Ψ : iProp Σ :=
    spmc_stack.(spmc_stack_inv) t γ.(base) (ws_bag_of_spmc_stack_namespace_base ι) ∗
    inv (ws_bag_of_spmc_stack_namespace_extra ι) (ws_bag_of_spmc_stack_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_spmc_stack_model t γ sz : iProp Σ :=
    ∃ vs,
    ⌜sz = length vs⌝ ∗
    ws_bag_of_spmc_stack_ctl₂ γ vs ∗
    spmc_stack.(spmc_stack_model) t γ.(base) vs.

  #[local] Definition ws_bag_of_spmc_stack_owner t γ :=
    spmc_stack.(spmc_stack_producer) t γ.(base).

  #[local] Instance ws_bag_of_spmc_stack_inv_contractive t γ ι n :
    Proper (pointwise_relation val (dist_later n) ==> (≡{n}≡)) (ws_bag_of_spmc_stack_inv t γ ι).
  Proof.
    rewrite /ws_bag_of_spmc_stack_inv /ws_bag_of_spmc_stack_inv_inner. solve_contractive.
  Qed.
  #[local] Instance ws_bag_of_spmc_stack_inv_ne t γ ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bag_of_spmc_stack_inv t γ ι).
  Proof.
    intros Ψ1 Ψ2 HΨ. f_equiv. intros v. apply dist_dist_later. done.
  Qed.
  #[local] Instance ws_bag_of_spmc_stack_inv_persistent t γ ι Ψ :
    Persistent (ws_bag_of_spmc_stack_inv t γ ι Ψ).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_spmc_stack_model_timeless t γ sz :
    Timeless (ws_bag_of_spmc_stack_model t γ sz).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_spmc_stack_owner_timeless t γ :
    Timeless (ws_bag_of_spmc_stack_owner t γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_owner_exclusive t γ :
    ws_bag_of_spmc_stack_owner t γ -∗
    ws_bag_of_spmc_stack_owner t γ -∗
    False.
  Proof.
    apply spmc_stack_producer_exclusive.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_make_spec ι Ψ :
    {{{ True }}}
      ws_bag_of_spmc_stack_make #()
    {{{ t γ,
      RET t;
      ws_bag_of_spmc_stack_inv t γ ι Ψ ∗
      ws_bag_of_spmc_stack_model t γ 0 ∗
      ws_bag_of_spmc_stack_owner t γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (spmc_stack_make_spec with "[//]"). iIntros "%t %γ_deque (#Hinv_deque & Hmodel_deque & Howner)".
    iMod (auth_excl_alloc' []) as "(%γ_extra & Hctl₂ & Hctl₁)".
    iApply ("HΦ" $! t (γ_deque, γ_extra)). iFrame. iSplitL "Hctl₁".
    - iFrame "#". iApply inv_alloc. iNext. iExists []. iFrame. done.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ ∗
      ws_bag_of_spmc_stack_owner t γ ∗
      Ψ v |
      ∀∀ sz, ws_bag_of_spmc_stack_model t γ sz
    >>>
      ws_bag_of_spmc_stack_push t v
      @ ↑ ι
    <<<
      ws_bag_of_spmc_stack_model t γ (S sz) |
      RET #(); ws_bag_of_spmc_stack_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner & Hv) HΦ".
    awp_apply (spmc_stack_push_spec with "[$Hinv_deque $Howner]").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := v :: vs.
      iIntros "Hmodel_deque".
      iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
      iModIntro. iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs'. auto with iFrame. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ ∗
      ws_bag_of_spmc_stack_owner t γ |
      ∀∀ sz, ws_bag_of_spmc_stack_model t γ sz
    >>>
      ws_bag_of_spmc_stack_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_spmc_stack_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_spmc_stack_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      ws_bag_of_spmc_stack_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner) HΦ".
    wp_rec.
    awp_apply (spmc_stack_pop_spec with "Hinv_deque").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%v & %vs' & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit; first done.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ |
      ∀∀ sz, ws_bag_of_spmc_stack_model t γ sz
    >>>
      ws_bag_of_spmc_stack_steal t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_spmc_stack_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_spmc_stack_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hinv_deque & #Hinv_extra) HΦ".
    wp_rec.
    awp_apply (spmc_stack_pop_spec with "Hinv_deque").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%v & %vs' & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit; first done.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  Definition ws_bag_of_spmc_stack :=
    Build_ws_bag
      ws_bag_of_spmc_stack_owner_exclusive
      ws_bag_of_spmc_stack_make_spec
      ws_bag_of_spmc_stack_push_spec
      ws_bag_of_spmc_stack_pop_spec
      ws_bag_of_spmc_stack_steal_spec.
End ws_bag_of_spmc_stack.

Class WsBagOfSpmcQueueG Σ `{!heapGS Σ} := {
  ws_bag_of_spmc_queue_G_ctl_G : AuthExclG Σ (listO valO) ;
}.
#[local] Existing Instance ws_bag_of_spmc_queue_G_ctl_G.

Definition ws_bag_of_spmc_queue_Σ := #[
  auth_excl_Σ (listO valO)
].
Lemma subG_ws_bag_of_spmc_queue_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_spmc_queue_Σ Σ →
  WsBagOfSpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_spmc_queue.
  Context `{WsBagOfSpmcQueueG Σ} (spmc_queue : spmc_queue Σ).
  Implicit Types γ : spmc_queue.(spmc_queue_name) * gname.

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_spmc_queue_meta_ctl := (nroot .@ "ctl").

  Notation ws_bag_of_spmc_queue_namespace_base ι := (ι .@ "base").
  Notation ws_bag_of_spmc_queue_namespace_extra ι := (ι .@ "extra").

  #[local] Definition ws_bag_of_spmc_queue_make :=
    spmc_queue.(spmc_queue_make).

  #[local] Definition ws_bag_of_spmc_queue_push :=
    spmc_queue.(spmc_queue_push).

  #[local] Definition ws_bag_of_spmc_queue_pop : val :=
    λ: "t",
      let: "o" := spmc_queue.(spmc_queue_pop) "t" in
      "o".

  #[local] Definition ws_bag_of_spmc_queue_steal : val :=
    λ: "t",
      let: "o" := spmc_queue.(spmc_queue_pop) "t" in
      "o".

  #[local] Definition ws_bag_of_spmc_queue_ctl₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_spmc_queue_ctl₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_spmc_queue_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_spmc_queue_ctl₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_spmc_queue_inv t γ ι Ψ : iProp Σ :=
    spmc_queue.(spmc_queue_inv) t γ.(base) (ws_bag_of_spmc_queue_namespace_base ι) ∗
    inv (ws_bag_of_spmc_queue_namespace_extra ι) (ws_bag_of_spmc_queue_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_spmc_queue_model t γ sz : iProp Σ :=
    ∃ vs,
    ⌜sz = length vs⌝ ∗
    ws_bag_of_spmc_queue_ctl₂ γ vs ∗
    spmc_queue.(spmc_queue_model) t γ.(base) vs.

  #[local] Definition ws_bag_of_spmc_queue_owner t γ :=
    spmc_queue.(spmc_queue_producer) t γ.(base).

  #[local] Instance ws_bag_of_spmc_queue_inv_contractive t γ ι n :
    Proper (pointwise_relation val (dist_later n) ==> (≡{n}≡)) (ws_bag_of_spmc_queue_inv t γ ι).
  Proof.
    rewrite /ws_bag_of_spmc_queue_inv /ws_bag_of_spmc_queue_inv_inner. solve_contractive.
  Qed.
  #[local] Instance ws_bag_of_spmc_queue_inv_ne t γ ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bag_of_spmc_queue_inv t γ ι).
  Proof.
    intros Ψ1 Ψ2 HΨ. f_equiv. intros v. apply dist_dist_later. done.
  Qed.
  #[local] Instance ws_bag_of_spmc_queue_inv_persistent t γ ι Ψ :
    Persistent (ws_bag_of_spmc_queue_inv t γ ι Ψ).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_spmc_queue_model_timeless t γ sz :
    Timeless (ws_bag_of_spmc_queue_model t γ sz).
  Proof.
    apply _.
  Qed.
  #[local] Instance ws_bag_of_spmc_queue_owner_timeless t γ :
    Timeless (ws_bag_of_spmc_queue_owner t γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_owner_exclusive t γ :
    ws_bag_of_spmc_queue_owner t γ -∗
    ws_bag_of_spmc_queue_owner t γ -∗
    False.
  Proof.
    apply spmc_queue_producer_exclusive.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_make_spec ι Ψ :
    {{{ True }}}
      ws_bag_of_spmc_queue_make #()
    {{{ t γ,
      RET t;
      ws_bag_of_spmc_queue_inv t γ ι Ψ ∗
      ws_bag_of_spmc_queue_model t γ 0 ∗
      ws_bag_of_spmc_queue_owner t γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd.
    wp_apply (spmc_queue_make_spec with "[//]"). iIntros "%t %γ_deque (#Hinv_deque & Hmodel_deque & Howner)".
    iMod (auth_excl_alloc' []) as "(%γ_extra & Hctl₂ & Hctl₁)".
    iApply ("HΦ" $! t (γ_deque, γ_extra)). iFrame. iSplitL "Hctl₁".
    - iFrame "#". iApply inv_alloc. iNext. iExists []. iFrame. done.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ ∗
      ws_bag_of_spmc_queue_owner t γ ∗
      Ψ v |
      ∀∀ sz, ws_bag_of_spmc_queue_model t γ sz
    >>>
      ws_bag_of_spmc_queue_push t v
      @ ↑ ι
    <<<
      ws_bag_of_spmc_queue_model t γ (S sz) |
      RET #(); ws_bag_of_spmc_queue_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner & Hv) HΦ".
    awp_apply (spmc_queue_push_spec with "[$Hinv_deque $Howner]").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := v :: vs.
      iIntros "Hmodel_deque".
      iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
      iModIntro. iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs'. auto with iFrame. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ ∗
      ws_bag_of_spmc_queue_owner t γ |
      ∀∀ sz, ws_bag_of_spmc_queue_model t γ sz
    >>>
      ws_bag_of_spmc_queue_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_spmc_queue_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_spmc_queue_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      ws_bag_of_spmc_queue_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hinv_deque & #Hinv_extra) & Howner) HΦ".
    wp_rec.
    awp_apply (spmc_queue_pop_spec with "Hinv_deque").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%vs' & %v & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit.
          { rewrite app_length (comm Nat.add) //. }
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ |
      ∀∀ sz, ws_bag_of_spmc_queue_model t γ sz
    >>>
      ws_bag_of_spmc_queue_steal t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜sz = 0 ∧ o = None⌝ ∗ ws_bag_of_spmc_queue_model t γ 0) ∨
      (∃ sz' v, ⌜sz = S sz' ∧ o = Some v⌝ ∗ ws_bag_of_spmc_queue_model t γ sz') |
      RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hinv_deque & #Hinv_extra) HΦ".
    wp_rec.
    awp_apply (spmc_queue_pop_spec with "Hinv_deque").
    iInv "Hinv_extra" as "(%vs & >Hctl₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj.
    iIntros "%sz (%_vs & -> & Hctl₂ & Hmodel_deque)".
    iDestruct (auth_excl_both_agree_L with "Hctl₂ Hctl₁") as %->.
    iAaccIntro with "Hmodel_deque".
    - iIntros "Hmodel_deque !>". iSplitL "Hctl₂ Hmodel_deque".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros "%o [((-> & ->) & Hmodel_deque) | (%vs' & %v & (-> & ->) & Hmodel_deque)]".
      + iModIntro. iExists None. iSplitL "Hctl₂ Hmodel_deque".
        { iLeft. iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hctl₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto.
      + iMod (auth_excl_update' vs' with "Hctl₂ Hctl₁") as "(Hctl₂ & Hctl₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hctl₂ Hmodel_deque".
        { iRight. iExists (length vs'), v. iSplit.
          { rewrite app_length (comm Nat.add) //. }
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hctl₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  Definition ws_bag_of_spmc_queue :=
    Build_ws_bag
      ws_bag_of_spmc_queue_owner_exclusive
      ws_bag_of_spmc_queue_make_spec
      ws_bag_of_spmc_queue_push_spec
      ws_bag_of_spmc_queue_pop_spec
      ws_bag_of_spmc_queue_steal_spec.
End ws_bag_of_spmc_queue.
