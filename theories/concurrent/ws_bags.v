From caml5 Require Import
  prelude.
From caml5.bi Require Import
  big_op.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  counter.
From caml5.concurrent Require Import
  ws_deques.

Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Record ws_bags `{!heapGS Σ} `{counter_G : !CounterG Σ} {unboxed : bool} := {
  ws_bags_make : val ;
  ws_bags_size : val ;
  ws_bags_push : val ;
  ws_bags_pop : val ;
  ws_bags_steal : val ;

  ws_bags_name : Type ;
  ws_bags_name_eq_dec :
    EqDecision ws_bags_name ;
  ws_bags_name_countable :
    Countable ws_bags_name ;

  ws_bags_inv : val → ws_bags_name → namespace → val → nat → (val → iProp Σ) → iProp Σ ;
  ws_bags_model : val → ws_bags_name → list nat → iProp Σ ;

  ws_bags_inv_ne t γ ι cntr sz n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bags_inv t γ ι cntr sz) ;
  ws_bags_inv_persistent t γ ι cntr sz Ψ :
    Persistent (ws_bags_inv t γ ι cntr sz Ψ) ;
  ws_bags_model_timeless t γ pots :
    Timeless (ws_bags_model t γ pots) ;

  ws_bags_inv_valid t γ ι cntr sz Ψ :
    ws_bags_inv t γ ι cntr sz Ψ -∗
    ∃ ι_cntr, counter_inv cntr ι_cntr (Some sz) ;

  ws_bags_make_spec ι Ψ cntr ι_cntr sz sz' :
    sz' = Z.of_nat sz →
    {{{
      counter_inv cntr ι_cntr (Some sz)
    }}}
      ws_bags_make #sz'
    {{{ t γ,
      RET t;
      ws_bags_inv t γ ι cntr sz Ψ ∗
      ws_bags_model t γ (replicate sz 0)
    }}} ;

  ws_bags_size_spec t γ ι cntr sz Ψ :
    {{{
      ws_bags_inv t γ ι cntr sz Ψ
    }}}
      ws_bags_size t
    {{{
      RET #sz; True
    }}} ;

  ws_bags_push_spec t γ ι cntr sz Ψ i i' v :
    i' = Z.of_nat i →
    <<<
      ws_bags_inv t γ ι cntr sz Ψ ∗
      counter_token cntr i ∗
      Ψ v
    | ∀∀ pots, ws_bags_model t γ pots
    >>>
      ws_bags_push t #i' v @ ↑ι
    <<< ∃∃ pot,
      ⌜pots !! i = Some pot⌝ ∗
      ws_bags_model t γ (<[i := S pot]> pots)
    | RET #(); counter_token cntr i
    >>> ;

  ws_bags_pop_spec t γ ι cntr sz Ψ i i' :
    i' = Z.of_nat i →
    <<<
      ws_bags_inv t γ ι cntr sz Ψ ∗
      counter_token cntr i
    | ∀∀ pots, ws_bags_model t γ pots
    >>>
      ws_bags_pop t #i' @ ↑ι
    <<< ∃∃ o,
        ⌜pots !! i = Some 0 ∧ o = None⌝ ∗
        ws_bags_model t γ pots
      ∨ ∃ pot v,
        ⌜pots !! i = Some (S pot) ∧ o = Some v⌝ ∗
        ws_bags_model t γ (<[i := pot]> pots)
    | RET from_option (λ v, SOMEV v) NONEV o;
      counter_token cntr i ∗
      from_option Ψ True o
    >>> ;

  ws_bags_steal_spec t γ ι cntr Ψ (sz : nat) i :
    (0 ≤ i < sz)%Z →
    <<<
      ws_bags_inv t γ ι cntr sz Ψ
    | ∀∀ pots, ws_bags_model t γ pots
    >>>
      ws_bags_steal t #i @ ↑ι
    <<< ∃∃ o,
      let i := Z.to_nat i in
        ⌜pots !! i = Some 0 ∧ o = None⌝ ∗
        ws_bags_model t γ pots
      ∨ ∃ pot v,
        ⌜pots !! i = Some (S pot) ∧ o = Some v⌝ ∗
        ws_bags_model t γ (<[i := pot]> pots)
    | RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>> ;

  ws_bags_unboxed :
    if unboxed then ∀ t γ ι cntr sz Ψ,
      ws_bags_inv t γ ι cntr sz Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_bags _ {_ _} _ : assert.
#[global] Arguments Build_ws_bags {_ _ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.
#[global] Existing Instance ws_bags_name_eq_dec.
#[global] Existing Instance ws_bags_name_countable.
#[global] Existing Instance ws_bags_inv_ne.
#[global] Existing Instance ws_bags_inv_persistent.
#[global] Existing Instance ws_bags_model_timeless.

#[global] Instance ws_bags_inv_proper `{!heapGS Σ} `{counter_G : !CounterG Σ} {unboxed} (ws_bags : ws_bags Σ unboxed) t γ ι cntr sz :
  Proper (pointwise_relation val (≡) ==> (≡)) (ws_bags.(ws_bags_inv) t γ ι cntr sz).
Proof.
  intros Ψ1 Ψ2 HΨ.
  rewrite /pointwise_relation in HΨ. setoid_rewrite equiv_dist in HΨ.
  rewrite equiv_dist. intros n. f_equiv. intros v. done.
Qed.

Class WsBagsOfWsDequesG Σ `{!heapGS Σ} `{counter_G : !CounterG Σ} := {
  ws_bags_of_ws_deques_G_model_G : AuthExclG Σ (leibnizO (list $ list val)) ;
}.
#[local] Existing Instance ws_bags_of_ws_deques_G_model_G.

Definition ws_bags_of_ws_deques_Σ := #[
  auth_excl_Σ (leibnizO (list $ list val))
].
Lemma subG_ws_bags_of_ws_deques_Σ Σ `{!heapGS Σ} `{counter_G : !CounterG Σ} :
  subG ws_bags_of_ws_deques_Σ Σ →
  WsBagsOfWsDequesG Σ.
Proof.
  solve_inG.
Qed.

Section ws_bags_of_ws_deques.
  Context `{ws_bags_of_ws_deques_G : WsBagsOfWsDequesG Σ}.
  Context {unboxed} (ws_deques : ws_deques Σ unboxed).
  Implicit Types γ : ws_deques.(ws_deques_name) * gname.

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(extra)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Notation ws_bags_of_ws_deques_namespace_base ι :=
    (ι .@ "base").
  Notation ws_bags_of_ws_deques_namespace_extra ι :=
    (ι .@ "extra").

  #[local] Definition ws_bags_of_ws_deques_make :=
    ws_deques.(ws_deques_make).

  #[local] Definition ws_bags_of_ws_deques_size :=
    ws_deques.(ws_deques_size).

  #[local] Definition ws_bags_of_ws_deques_push :=
    ws_deques.(ws_deques_push).

  #[local] Definition ws_bags_of_ws_deques_pop : val :=
    λ: "t" "i",
      let: "o" := ws_deques.(ws_deques_pop) "t" "i" in
      "o".

  #[local] Definition ws_bags_of_ws_deques_steal : val :=
    λ: "t" "i",
      let: "o" := ws_deques.(ws_deques_steal) "t" "i" in
      "o".

  #[local] Definition ws_bags_of_ws_deques_model₁ γ vss :=
    auth_excl_frag (auth_excl_G := ws_bags_of_ws_deques_G_model_G) γ.(extra) vss.
  #[local] Definition ws_bags_of_ws_deques_model₂ γ vss :=
    auth_excl_auth (auth_excl_G := ws_bags_of_ws_deques_G_model_G) γ.(extra) (DfracOwn 1) vss.

  #[local] Definition ws_bags_of_ws_deques_inv_inner γ Ψ : iProp Σ :=
    ∃ vss,
    ws_bags_of_ws_deques_model₁ γ vss ∗
    [∗ list] vs ∈ vss, [∗ list] v ∈ vs, Ψ v.
  #[local] Definition ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ : iProp Σ :=
    ws_deques.(ws_deques_inv) t γ.(base) (ws_bags_of_ws_deques_namespace_base ι) cntr sz ∗
    inv (ws_bags_of_ws_deques_namespace_extra ι) (ws_bags_of_ws_deques_inv_inner γ Ψ).

  #[local] Definition ws_bags_of_ws_deques_model t γ pots : iProp Σ :=
    ∃ vss,
    ⌜Forall2 (λ vs pot, length vs = pot) vss pots⌝ ∗
    ws_bags_of_ws_deques_model₂ γ vss ∗
    ws_deques.(ws_deques_model) t γ.(base) vss.

  #[local] Instance ws_bags_of_ws_deques_inv_contractive t γ ι cntr sz n :
    Proper (pointwise_relation val (dist_later n) ==> (≡{n}≡)) (ws_bags_of_ws_deques_inv t γ ι cntr sz).
  Proof.
    rewrite /ws_bags_of_ws_deques_inv /ws_bags_of_ws_deques_inv_inner. solve_contractive.
  Qed.
  #[local] Instance ws_bags_of_ws_deques_inv_ne t γ ι cntr sz n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (ws_bags_of_ws_deques_inv t γ ι cntr sz).
  Proof.
    intros Ψ1 Ψ2 HΨ. f_equiv. intros v. apply dist_dist_later. done.
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_inv_valid t γ ι cntr sz Ψ :
    ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ -∗
    ∃ ι_cntr, counter_inv cntr ι_cntr (Some sz).
  Proof.
    iIntros "(#Hbase_inv & _)".
    iApply (ws_deques_inv_valid with "Hbase_inv").
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_make_spec ι Ψ cntr ι_cntr sz sz' :
    sz' = Z.of_nat sz →
    {{{
      counter_inv cntr ι_cntr (Some sz)
    }}}
      ws_bags_of_ws_deques_make #sz'
    {{{ t γ,
      RET t;
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ ∗
      ws_bags_of_ws_deques_model t γ (replicate sz 0)
    }}}.
  Proof.
    iIntros (->) "%Φ #Hinv HΦ".
    iApply wp_fupd. wp_apply (ws_deques_make_spec with "[//]"); first done. iIntros "%t %γ_base (#Hbase_inv & Hbase_model)".
    set vss := replicate sz [].
    iMod (auth_excl_alloc' (auth_excl_G := ws_bags_of_ws_deques_G_model_G) vss) as "(%γ_extra & Hmodel₂ & Hmodel₁)".
    iApply ("HΦ" $! t (γ_base, γ_extra)). iFrame. iSplitL "Hmodel₁".
    - iFrame "#∗". iApply inv_alloc. iExists vss. iFrame.
      iApply big_sepL_replicate_2. iApply big_sepL_intro. auto.
    - iExists vss. iFrame. iPureIntro. apply Forall2_replicate. done.
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_size_spec t γ ι cntr sz Ψ :
    {{{
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ
    }}}
      ws_bags_of_ws_deques_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iIntros "%Φ (#Hbase_inv & #Hinv) HΦ".
    wp_apply (ws_deques_size_spec with "Hbase_inv"). done.
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_push_spec t γ ι cntr sz Ψ i i' v :
    i' = Z.of_nat i →
    <<<
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ ∗
      counter_token cntr i ∗
      Ψ v
    | ∀∀ pots, ws_bags_of_ws_deques_model t γ pots
    >>>
      ws_bags_of_ws_deques_push t #i' v @ ↑ι
    <<< ∃∃ pot,
      ⌜pots !! i = Some pot⌝ ∗
      ws_bags_of_ws_deques_model t γ (<[i := S pot]> pots)
    | RET #(); counter_token cntr i
    >>>.
  Proof.
    iIntros (->) "!> %Φ ((#Hbase_inv & #Hinv) & Htoken_cntr & HΨ) HΦ".
    awp_apply (ws_deques_push_spec with "[$Hbase_inv $Htoken_cntr]"); first done.
    iInv "Hinv" as "(%vss & >Hmodel₁ & HΨss)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pots (%_vss & %Hpots & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vss. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vss. auto with iFrame.
    - iIntros "%vs (% & Hbase_model)". list_simplifier.
      set vss' := <[i := vs ++ [v]]> vss.
      iMod (auth_excl_update' (auth_excl_G := ws_bags_of_ws_deques_G_model_G) vss' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iModIntro. iExists (length vs). iSplitL "Hmodel₂ Hbase_model".
      { iSplit; first done. iExists vss'. iFrame. iPureIntro.
        apply Forall2_insert; first done. rewrite app_length /=. lia.
      }
      iIntros "$ !> !>". iExists vss'. iFrame.
      iApply (big_sepL_mono_strong with "HΨss"); first rewrite insert_length //.
      iApply (big_sepL_delete'_2 with "[HΨ]").
      { rewrite lookup_seq_lt //. eapply lookup_lt_Some. done. }
      + iIntros (? ? (? & [(_ & <- & _) |]%list_lookup_insert_Some )) "HΨs"; last naive_solver. list_simplifier.
        iFrame. done.
      + iApply big_sepL_intro. iIntros "!>" (j ? (-> & _)%lookup_seq Hj ? ? (? & ?%list_lookup_insert_Some)) "HΨ"; naive_solver.
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_pop_spec t γ ι cntr sz Ψ i i' :
    i' = Z.of_nat i →
    <<<
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ ∗
      counter_token cntr i
    | ∀∀ pots, ws_bags_of_ws_deques_model t γ pots
    >>>
      ws_bags_of_ws_deques_pop t #i' @ ↑ι
    <<< ∃∃ o,
        ⌜pots !! i = Some 0 ∧ o = None⌝ ∗
        ws_bags_of_ws_deques_model t γ pots
      ∨ ∃ pot v,
        ⌜pots !! i = Some (S pot) ∧ o = Some v⌝ ∗
        ws_bags_of_ws_deques_model t γ (<[i := pot]> pots)
    | RET from_option (λ v, SOMEV v) NONEV o;
      counter_token cntr i ∗
      from_option Ψ True o
    >>>.
  Proof.
    iIntros (->) "!> %Φ ((#Hbase_inv & #Hinv) & Htoken_cntr) HΦ".
    wp_rec.
    awp_smart_apply (ws_deques_pop_spec with "[$Hbase_inv $Htoken_cntr]"); first done.
    iInv "Hinv" as "(%vss & >Hmodel₁ & HΨss)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pots (%_vss & %Hpots & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vss. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vss. auto with iFrame.
    - iIntros "%o [((% & ->) & Hbase_model) | (%vs & %v & (% & ->) & Hbase_model)]"; list_simplifier.
      + iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iLeft. iSplitR; first done. iExists vss. auto with iFrame. }
        iIntros "!> HΦ !>". iSplitR "HΦ"; first (iExists vss; iFrame). iIntros "Htoken_cntr".
        wp_pures.
        iApply ("HΦ" with "[$Htoken_cntr //]").
      + set vss' := <[i := vs]> vss.
        iMod (auth_excl_update' (auth_excl_G := ws_bags_of_ws_deques_G_model_G) vss' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct (big_sepL_insert_acc with "HΨss") as "(HΨs & HΨss)"; first done.
        iDestruct "HΨs" as "(HΨs & HΨ & _)".
        iSpecialize ("HΨss" with "HΨs").
        iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iRight. iExists (length vs), v. iSplitR.
          { rewrite -Nat.add_1_r -(app_length vs [v]) //. }
          iExists vss'. iFrame. iPureIntro. apply Forall2_insert; done.
        }
        iIntros "!> HΦ !>". iSplitR "HΨ HΦ"; first (iExists vss'; iFrame). iIntros "Htoken_cntr".
        wp_pures.
        iApply ("HΦ" with "[$Htoken_cntr $HΨ]").
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_steal_spec t γ ι cntr Ψ (sz : nat) i :
    (0 ≤ i < sz)%Z →
    <<<
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ
    | ∀∀ pots, ws_bags_of_ws_deques_model t γ pots
    >>>
      ws_bags_of_ws_deques_steal t #i @ ↑ι
    <<< ∃∃ o,
      let i := Z.to_nat i in
        ⌜pots !! i = Some 0 ∧ o = None⌝ ∗
        ws_bags_of_ws_deques_model t γ pots
      ∨ ∃ pot v,
        ⌜pots !! i = Some (S pot) ∧ o = Some v⌝ ∗
        ws_bags_of_ws_deques_model t γ (<[i := pot]> pots)
    | RET from_option (λ v, SOMEV v) NONEV o;
      from_option Ψ True o
    >>>.
  Proof.
    iIntros "% !> %Φ (#Hbase_inv & #Hinv) HΦ".
    wp_rec.
    awp_smart_apply (ws_deques_steal_spec with "Hbase_inv"); first done.
    iInv "Hinv" as "(%vss & >Hmodel₁ & HΨss)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%pots (%_vss & %Hpots & Hmodel₂ & Hbase_model)".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAaccIntro with "Hbase_model".
    - iIntros "Hbase_model !>". iSplitL "Hmodel₂ Hbase_model".
      { iExists vss. auto with iFrame. }
      iIntros "$ !>". iFrame. iExists vss. auto with iFrame.
    - iIntros "%o [((% & ->) & Hbase_model) | (%v & %vs & (% & ->) & Hbase_model)]"; list_simplifier.
      + iExists None. iSplitL "Hmodel₂ Hbase_model".
        { iLeft. iSplitR; first done. iExists vss. auto with iFrame. }
        iIntros "!> HΦ !>". iSplitR "HΦ"; first (iExists vss; iFrame). iIntros "Htoken_cntr".
        wp_pures.
        iApply ("HΦ" with "[$Htoken_cntr //]").
      + set (vss' := <[Z.to_nat i := vs]> vss).
        iMod (auth_excl_update' (auth_excl_G := ws_bags_of_ws_deques_G_model_G) vss' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iDestruct (big_sepL_insert_acc with "HΨss") as "(HΨs & HΨss)"; first done.
        iDestruct "HΨs" as "(HΨ & HΨs)".
        iSpecialize ("HΨss" with "HΨs").
        iExists (Some v). iSplitL "Hmodel₂ Hbase_model".
        { iRight. iExists (length vs), v. iSplitR; first done.
          iExists vss'. iFrame. iPureIntro. apply Forall2_insert; done.
        }
        iIntros "!> HΦ !>". iSplitR "HΨ HΦ"; first (iExists vss'; iFrame). iIntros "Htoken_cntr".
        wp_pures.
        iApply ("HΦ" with "HΨ").
  Qed.

  #[local] Lemma ws_bags_of_ws_deques_unboxed :
    if unboxed then ∀ t γ ι cntr sz Ψ,
      ws_bags_of_ws_deques_inv t γ ι cntr sz Ψ -∗
      ⌜val_is_unboxed t⌝
    else
      True.
  Proof.
    move: ws_deques.(ws_deques_unboxed).
    refine (match unboxed with true => _ | false => _ end); last done.
    iIntros "%Hunboxed * (#Hbase_inv & #Hinv)".
    iApply (Hunboxed with "Hbase_inv").
  Qed.

  Definition ws_bags_of_ws_deques :=
    Build_ws_bags unboxed
      ws_bags_of_ws_deques_inv_valid
      ws_bags_of_ws_deques_make_spec
      ws_bags_of_ws_deques_size_spec
      ws_bags_of_ws_deques_push_spec
      ws_bags_of_ws_deques_pop_spec
      ws_bags_of_ws_deques_steal_spec
      ws_bags_of_ws_deques_unboxed.
End ws_bags_of_ws_deques.
