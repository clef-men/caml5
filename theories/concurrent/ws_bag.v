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
  mpmc_stack
  mpmc_queue
  spmc_stack
  spmc_queue
  ws_deque.

Implicit Types v t : val.

Record ws_bag `{!heapGS Σ} {unboxed : bool} := {
  ws_bag_make : val ;
  ws_bag_push : val ;
  ws_bag_pop : val ;
  ws_bag_steal : val ;

  ws_bag_name : Type ;
  ws_bag_name_eq_dec :
    EqDecision ws_bag_name ;
  ws_bag_name_countable :
    Countable ws_bag_name ;

  ws_bag_inv : val → ws_bag_name → namespace → (val → iProp Σ) → iProp Σ ;
  ws_bag_model : val → ws_bag_name → nat → iProp Σ ;
  ws_bag_owner : val → ws_bag_name → iProp Σ ;

  ws_bag_inv_ne t γ ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bag_inv t γ ι) ;
  ws_bag_inv_persistent t γ ι Ψ :
    Persistent (ws_bag_inv t γ ι Ψ) ;
  ws_bag_model_timeless t γ pot :
    Timeless (ws_bag_model t γ pot) ;
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
      ws_bag_owner t γ ∗
      Ψ v
    | ∀∀ pot, ws_bag_model t γ pot
    >>>
      ws_bag_push t v @ ↑ι
    <<<
      ws_bag_model t γ (S pot)
    | RET #();
      ws_bag_owner t γ
    >>> ;

  ws_bag_pop_spec t γ ι Ψ :
    <<<
      ws_bag_inv t γ ι Ψ ∗
      ws_bag_owner t γ
    | ∀∀ pot, ws_bag_model t γ pot
    >>>
      ws_bag_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_model t γ pot'
      end
    | RET o;
      ws_bag_owner t γ ∗
      from_option Ψ True o
    >>> ;

  ws_bag_steal_spec t γ ι Ψ :
    <<<
      ws_bag_inv t γ ι Ψ
    | ∀∀ pot, ws_bag_model t γ pot
    >>>
      ws_bag_steal t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_model t γ pot'
      end
    | RET o;
      from_option Ψ True o
    >>> ;

  ws_bag_unboxed :
    if unboxed then ∀ t γ ι Ψ,
      ws_bag_inv t γ ι Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_bag _ {_} _ : assert.
#[global] Arguments Build_ws_bag {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ : assert.
#[global] Existing Instance ws_bag_name_eq_dec.
#[global] Existing Instance ws_bag_name_countable.
#[global] Existing Instance ws_bag_inv_ne.
#[global] Existing Instance ws_bag_inv_persistent.
#[global] Existing Instance ws_bag_model_timeless.
#[global] Existing Instance ws_bag_owner_timeless.

#[global] Instance ws_bag_inv_proper `{!heapGS Σ} {unboxed} (ws_bag : ws_bag Σ unboxed) t γ ι :
  Proper (pointwise_relation val (≡) ==> (≡)) (ws_bag.(ws_bag_inv) t γ ι).
Proof.
  intros Ψ1 Ψ2 HΨ.
  rewrite /pointwise_relation in HΨ. setoid_rewrite equiv_dist in HΨ.
  rewrite equiv_dist. intros n. f_equiv. intros v. done.
Qed.

Class WsBagOfWsDequeG Σ `{!heapGS Σ} := {
  ws_bag_of_ws_deque_G_model_G : AuthExclG Σ (leibnizO (list val)) ;
}.
#[local] Existing Instance ws_bag_of_ws_deque_G_model_G.

Definition ws_bag_of_ws_deque_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
Lemma subG_ws_bag_of_ws_deque_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_ws_deque_Σ Σ →
  WsBagOfWsDequeG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_ws_deque.
  Context `{ws_bag_of_ws_deque_G : WsBagOfWsDequeG Σ}.
  Context {unboxed} (ws_deque : ws_deque Σ unboxed).

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

  Implicit Types γ : ws_deque.(ws_deque_name) * gname.
  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_ws_deque_namespace_base ι := (ι .@ "base").
  Notation ws_bag_of_ws_deque_namespace_extra ι := (ι .@ "extra").

  #[local] Definition ws_bag_of_ws_deque_model₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_ws_deque_model₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_ws_deque_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_ws_deque_model₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_ws_deque_inv t γ ι Ψ : iProp Σ :=
    ws_deque.(ws_deque_inv) t γ.(base) (ws_bag_of_ws_deque_namespace_base ι) ∗
    inv (ws_bag_of_ws_deque_namespace_extra ι) (ws_bag_of_ws_deque_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_ws_deque_model t γ pot : iProp Σ :=
    ∃ vs,
    ⌜pot = length vs⌝ ∗
    ws_bag_of_ws_deque_model₂ γ vs ∗
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
    wp_apply (ws_deque_make_spec with "[//]"). iIntros "%t %γ_base (#Hbase_inv & Hbase_model & Howner)".
    iMod (auth_excl_alloc' (auth_excl_G := ws_bag_of_ws_deque_G_model_G) []) as "(%γ_extra & Hmodel₂ & Hmodel₁)".
    iApply ("HΦ" $! t (γ_base, γ_extra)). iFrame. iSplitL "Hmodel₁".
    - iFrame "#∗". iApply inv_alloc. iExists []. auto.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ ∗
      ws_bag_of_ws_deque_owner t γ ∗
      Ψ v
    | ∀∀ pot, ws_bag_of_ws_deque_model t γ pot
    >>>
      ws_bag_of_ws_deque_push t v @ ↑ι
    <<<
      ws_bag_of_ws_deque_model t γ (S pot)
    | RET #();
      ws_bag_of_ws_deque_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner & Hv) HΦ".
    awp_apply (ws_deque_push_spec with "[$Hbase_inv $Howner]").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := vs ++ [v].
      iIntros "Hbase_model".
      iMod (auth_excl_update' (auth_excl_G := ws_bag_of_ws_deque_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iModIntro. iSplitL "Hmodel₂ Hbase_model".
      { iExists vs'. rewrite app_length /=. auto with iFrame lia. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ ∗
      ws_bag_of_ws_deque_owner t γ
    | ∀∀ pot, ws_bag_of_ws_deque_model t γ pot
    >>>
      ws_bag_of_ws_deque_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_ws_deque_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_ws_deque_model t γ pot'
      end
    | RET o;
      ws_bag_of_ws_deque_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner) HΦ".
    wp_rec.
    awp_apply (ws_deque_pop_spec with "[$Hbase_inv $Howner]").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_ws_deque_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first rewrite app_length (comm Nat.add) //.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_ws_deque_inv t γ ι Ψ
    | ∀∀ pot, ws_bag_of_ws_deque_model t γ pot
    >>>
      ws_bag_of_ws_deque_steal t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_ws_deque_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_ws_deque_model t γ pot'
      end
    | RET o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hbase_inv & #Hinv) HΦ".
    wp_rec.
    awp_apply (ws_deque_steal_spec with "Hbase_inv").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_ws_deque_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first done. iExists vs'. auto with iFrame. }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "Howner". wp_pures. iApply "HΦ". auto.
  Qed.

  #[local] Lemma ws_bag_of_ws_deque_unboxed :
    if unboxed then ∀ t γ ι Ψ,
      ws_bag_of_ws_deque_inv t γ ι Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True.
  Proof.
    move: ws_deque.(ws_deque_unboxed).
    refine (match unboxed with true => _ | false => _ end); last done.
    iIntros "%Hunboxed * (#Hbase_inv & #Hinv)".
    iApply (Hunboxed with "Hbase_inv").
  Qed.

  Definition ws_bag_of_ws_deque :=
    Build_ws_bag unboxed
      ws_bag_of_ws_deque_owner_exclusive
      ws_bag_of_ws_deque_make_spec
      ws_bag_of_ws_deque_push_spec
      ws_bag_of_ws_deque_pop_spec
      ws_bag_of_ws_deque_steal_spec
      ws_bag_of_ws_deque_unboxed.
End ws_bag_of_ws_deque.

Class WsBagOfSpmcStackG Σ `{!heapGS Σ} := {
  ws_bag_of_spmc_stack_G_model_G : AuthExclG Σ (leibnizO (list val)) ;
}.
#[local] Existing Instance ws_bag_of_spmc_stack_G_model_G.

Definition ws_bag_of_spmc_stack_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
Lemma subG_ws_bag_of_spmc_stack_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_spmc_stack_Σ Σ →
  WsBagOfSpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_spmc_stack.
  Context `{ws_bag_of_spmc_stack_G : WsBagOfSpmcStackG Σ}.
  Context {unboxed} (spmc_stack : spmc_stack Σ unboxed).

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

  Implicit Types γ : spmc_stack.(spmc_stack_name) * gname.
  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_spmc_stack_namespace_base ι :=
    (ι .@ "base").
  Notation ws_bag_of_spmc_stack_namespace_extra ι :=
    (ι .@ "extra").

  #[local] Definition ws_bag_of_spmc_stack_model₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_spmc_stack_model₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_spmc_stack_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_spmc_stack_model₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_spmc_stack_inv t γ ι Ψ : iProp Σ :=
    spmc_stack.(spmc_stack_inv) t γ.(base) (ws_bag_of_spmc_stack_namespace_base ι) ∗
    inv (ws_bag_of_spmc_stack_namespace_extra ι) (ws_bag_of_spmc_stack_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_spmc_stack_model t γ pot : iProp Σ :=
    ∃ vs,
    ⌜pot = length vs⌝ ∗
    ws_bag_of_spmc_stack_model₂ γ vs ∗
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
    wp_apply (spmc_stack_make_spec with "[//]"). iIntros "%t %γ_base (#Hbase_inv & Hbase_model & Howner)".
    iMod (auth_excl_alloc' (auth_excl_G := ws_bag_of_spmc_stack_G_model_G) []) as "(%γ_extra & Hmodel₂ & Hmodel₁)".
    iApply ("HΦ" $! t (γ_base, γ_extra)). iFrame. iSplitL "Hmodel₁".
    - iFrame "#∗". iApply inv_alloc. iExists []. auto.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ ∗
      ws_bag_of_spmc_stack_owner t γ ∗
      Ψ v
    | ∀∀ pot, ws_bag_of_spmc_stack_model t γ pot
    >>>
      ws_bag_of_spmc_stack_push t v @ ↑ι
    <<<
      ws_bag_of_spmc_stack_model t γ (S pot)
    | RET #();
      ws_bag_of_spmc_stack_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner & Hv) HΦ".
    awp_apply (spmc_stack_push_spec with "[$Hbase_inv $Howner]").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := v :: vs.
      iIntros "Hbase_model".
      iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_stack_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iModIntro. iSplitL "Hmodel₂ Hbase_model".
      { iExists vs'. auto with iFrame. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ ∗
      ws_bag_of_spmc_stack_owner t γ
    | ∀∀ pot, ws_bag_of_spmc_stack_model t γ pot
    >>>
      ws_bag_of_spmc_stack_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_spmc_stack_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_spmc_stack_model t γ pot'
      end
    | RET o;
      ws_bag_of_spmc_stack_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner) HΦ".
    wp_rec.
    awp_apply (spmc_stack_pop_spec with "Hbase_inv").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_stack_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first done. iExists vs'. auto with iFrame. }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_stack_inv t γ ι Ψ
    | ∀∀ pot, ws_bag_of_spmc_stack_model t γ pot
    >>>
      ws_bag_of_spmc_stack_steal t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_spmc_stack_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_spmc_stack_model t γ pot'
      end
    | RET o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hbase_inv & #Hinv) HΦ".
    wp_rec.
    awp_apply (spmc_stack_pop_spec with "Hbase_inv").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_stack_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hv & Hvs')".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first done. iExists vs'. auto with iFrame. }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto.
  Qed.

  #[local] Lemma ws_bag_of_spmc_stack_unboxed :
    if unboxed then ∀ t γ ι Ψ,
      ws_bag_of_spmc_stack_inv t γ ι Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True.
  Proof.
    move: spmc_stack.(spmc_stack_unboxed).
    refine (match unboxed with true => _ | false => _ end); last done.
    iIntros "%Hunboxed * (#Hbase_inv & #Hinv)".
    iApply (Hunboxed with "Hbase_inv").
  Qed.

  Definition ws_bag_of_spmc_stack :=
    Build_ws_bag unboxed
      ws_bag_of_spmc_stack_owner_exclusive
      ws_bag_of_spmc_stack_make_spec
      ws_bag_of_spmc_stack_push_spec
      ws_bag_of_spmc_stack_pop_spec
      ws_bag_of_spmc_stack_steal_spec
      ws_bag_of_spmc_stack_unboxed.
End ws_bag_of_spmc_stack.

Class WsBagOfMpmcStackG Σ `{!heapGS Σ} := {
  ws_bag_of_mpmc_stack_G_mpmc_stack_G : SpmcStackOfMpmcStackG Σ ;
  ws_bag_of_mpmc_stack_G_spmc_stack_G : WsBagOfSpmcStackG Σ ;
}.
#[local] Existing Instance ws_bag_of_mpmc_stack_G_mpmc_stack_G.
#[local] Existing Instance ws_bag_of_mpmc_stack_G_spmc_stack_G.

Definition ws_bag_of_mpmc_stack_Σ := #[
  spmc_stack_of_mpmc_stack_Σ ;
  ws_bag_of_spmc_stack_Σ
].
Lemma subG_ws_bag_of_mpmc_stack_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_mpmc_stack_Σ Σ →
  WsBagOfMpmcStackG Σ.
Proof.
  pose subG_spmc_stack_of_mpmc_stack_Σ.
  pose subG_ws_bag_of_spmc_stack_Σ.
  solve_inG.
Qed.

Definition ws_bag_of_mpmc_stack `{ws_bag_of_mpmc_stack_G : WsBagOfMpmcStackG Σ} {unboxed} (mpmc_stack : mpmc_stack Σ unboxed) :=
  ws_bag_of_spmc_stack (spmc_stack_of_mpmc_stack mpmc_stack).

Class WsBagOfSpmcQueueG Σ `{!heapGS Σ} := {
  ws_bag_of_spmc_queue_G_model_G : AuthExclG Σ (leibnizO (list val)) ;
}.
#[local] Existing Instance ws_bag_of_spmc_queue_G_model_G.

Definition ws_bag_of_spmc_queue_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
Lemma subG_ws_bag_of_spmc_queue_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_spmc_queue_Σ Σ →
  WsBagOfSpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bag_of_spmc_queue.
  Context `{ws_bag_of_spmc_queue_G : WsBagOfSpmcQueueG Σ}.
  Context {unboxed} (spmc_queue : spmc_queue Σ unboxed).

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

  Implicit Types γ : spmc_queue.(spmc_queue_name) * gname.
  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bag_of_spmc_queue_namespace_base ι :=
    (ι .@ "base").
  Notation ws_bag_of_spmc_queue_namespace_extra ι :=
    (ι .@ "extra").

  #[local] Definition ws_bag_of_spmc_queue_model₁ γ vs :=
    auth_excl_frag γ.(extra) vs.
  #[local] Definition ws_bag_of_spmc_queue_model₂ γ vs :=
    auth_excl_auth γ.(extra) (DfracOwn 1) vs.

  #[local] Definition ws_bag_of_spmc_queue_inv_inner γ Ψ : iProp Σ :=
    ∃ vs,
    ws_bag_of_spmc_queue_model₁ γ vs ∗
    [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bag_of_spmc_queue_inv t γ ι Ψ : iProp Σ :=
    spmc_queue.(spmc_queue_inv) t γ.(base) (ws_bag_of_spmc_queue_namespace_base ι) ∗
    inv (ws_bag_of_spmc_queue_namespace_extra ι) (ws_bag_of_spmc_queue_inv_inner γ Ψ).

  #[local] Definition ws_bag_of_spmc_queue_model t γ pot : iProp Σ :=
    ∃ vs,
    ⌜pot = length vs⌝ ∗
    ws_bag_of_spmc_queue_model₂ γ vs ∗
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
    wp_apply (spmc_queue_make_spec with "[//]"). iIntros "%t %γ_base (#Hbase_inv & Hbase_model & Howner)".
    iMod (auth_excl_alloc' (auth_excl_G := ws_bag_of_spmc_queue_G_model_G) []) as "(%γ_extra & Hmodel₂ & Hmodel₁)".
    iApply ("HΦ" $! t (γ_base, γ_extra)). iFrame. iSplitL "Hmodel₁".
    - iFrame "#∗". iApply inv_alloc. iExists []. auto.
    - iExists []. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_push_spec t γ ι Ψ v :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ ∗
      ws_bag_of_spmc_queue_owner t γ ∗
      Ψ v
    | ∀∀ pot, ws_bag_of_spmc_queue_model t γ pot
    >>>
      ws_bag_of_spmc_queue_push t v @ ↑ι
    <<<
      ws_bag_of_spmc_queue_model t γ (S pot)
    | RET #();
      ws_bag_of_spmc_queue_owner t γ
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner & Hv) HΦ".
    awp_apply (spmc_queue_push_spec with "[$Hbase_inv $Howner]").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. auto with iFrame.
    - set vs' := v :: vs.
      iIntros "Hbase_model".
      iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_queue_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iModIntro. iSplitL "Hmodel₂ Hbase_model".
      { iExists vs'. auto with iFrame. }
      iIntros "$ !>". iExists vs'. auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_pop_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ ∗
      ws_bag_of_spmc_queue_owner t γ
    | ∀∀ pot, ws_bag_of_spmc_queue_model t γ pot
    >>>
      ws_bag_of_spmc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_spmc_queue_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_spmc_queue_model t γ pot'
      end
    | RET o;
      ws_bag_of_spmc_queue_owner t γ ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ ((#Hbase_inv & #Hinv) & Howner) HΦ".
    wp_rec.
    awp_apply (spmc_queue_pop_spec with "Hbase_inv").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vs. iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_queue_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first rewrite app_length (comm Nat.add) //.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_steal_spec t γ ι Ψ :
    <<<
      ws_bag_of_spmc_queue_inv t γ ι Ψ
    | ∀∀ pot, ws_bag_of_spmc_queue_model t γ pot
    >>>
      ws_bag_of_spmc_queue_steal t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜pot = 0⌝ ∗
          ws_bag_of_spmc_queue_model t γ 0
      | Some v =>
          ∃ pot',
          ⌜pot = S pot'⌝ ∗
          ws_bag_of_spmc_queue_model t γ pot'
      end
    | RET o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "!> %Φ (#Hbase_inv & #Hinv) HΦ".
    wp_rec.
    awp_apply (spmc_queue_pop_spec with "Hbase_inv").
    iInv "Hinv" as "(%vs & >Hmodel₁ & Hvs)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pot (%_vs & -> & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vs. auto with iFrame. }
      iIntros "$ !>". iExists vs. auto with iFrame.
    - iIntros ([v |]).
      + iIntros "(%vs' & -> & Hbase_model)".
        iMod (auth_excl_update' (auth_excl_G := ws_bag_of_spmc_queue_G_model_G) vs' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct "Hvs" as "(Hvs' & Hv & _)".
        iModIntro. iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iExists (length vs'). iSplit; first rewrite app_length (comm Nat.add) //.
          iExists vs'. auto with iFrame.
        }
        iIntros "HΦ !>". iSplitL "Hmodel₁ Hvs'".
        { iExists vs'. auto with iFrame. }
        iIntros "_". wp_pures. iApply "HΦ". auto with iFrame.
      + iIntros "(-> & Hbase_model) !>".
        iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iSplit; first done. iExists []. auto with iFrame. }
        iIntros "HΦ !>". iFrame. iSplitL "Hmodel₁ Hvs".
        { iExists []. auto. }
        iIntros "_". wp_pures. iApply "HΦ". auto.
  Qed.

  #[local] Lemma ws_bag_of_spmc_queue_unboxed :
    if unboxed then ∀ t γ ι Ψ,
      ws_bag_of_spmc_queue_inv t γ ι Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True.
  Proof.
    move: spmc_queue.(spmc_queue_unboxed).
    refine (match unboxed with true => _ | false => _ end); last done.
    iIntros "%Hunboxed * (#Hbase_inv & #Hinv)".
    iApply (Hunboxed with "Hbase_inv").
  Qed.

  Definition ws_bag_of_spmc_queue :=
    Build_ws_bag unboxed
      ws_bag_of_spmc_queue_owner_exclusive
      ws_bag_of_spmc_queue_make_spec
      ws_bag_of_spmc_queue_push_spec
      ws_bag_of_spmc_queue_pop_spec
      ws_bag_of_spmc_queue_steal_spec
      ws_bag_of_spmc_queue_unboxed.
End ws_bag_of_spmc_queue.

Class WsBagOfMpmcQueueG Σ `{!heapGS Σ} := {
  ws_bag_of_mpmc_queue_G_mpmc_queue_G : SpmcQueueOfMpmcQueueG Σ ;
  ws_bag_of_mpmc_queue_G_spmc_queue_G : WsBagOfSpmcQueueG Σ ;
}.
#[local] Existing Instance ws_bag_of_mpmc_queue_G_mpmc_queue_G.
#[local] Existing Instance ws_bag_of_mpmc_queue_G_spmc_queue_G.

Definition ws_bag_of_mpmc_queue_Σ := #[
  spmc_queue_of_mpmc_queue_Σ ;
  ws_bag_of_spmc_queue_Σ
].
Lemma subG_ws_bag_of_mpmc_queue_Σ Σ `{!heapGS Σ} :
  subG ws_bag_of_mpmc_queue_Σ Σ →
  WsBagOfMpmcQueueG Σ.
Proof.
  pose subG_spmc_queue_of_mpmc_queue_Σ.
  pose subG_ws_bag_of_spmc_queue_Σ.
  solve_inG.
Qed.

Definition ws_bag_of_mpmc_queue
  `{ws_bag_of_mpmc_queue_G : WsBagOfMpmcQueueG Σ}
  {unboxed} (mpmc_queue : mpmc_queue Σ unboxed)
:=
  ws_bag_of_spmc_queue (spmc_queue_of_mpmc_queue mpmc_queue).
