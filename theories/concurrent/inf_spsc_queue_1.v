From Coq.Logic Require Import
  FunctionalExtensionality.

From iris.algebra Require Import
  list.

From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics
  list.
From caml5.base_logic Require Import
  lib.auth_excl
  lib.mono_list.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  record3.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  inf_array
  spsc_queue.

Class InfSpscQueueG Σ `{!heapGS Σ} (array : inf_array Σ false) := {
  #[local] inf_spsc_queue_G_producer_G :: AuthExclG Σ (natO * (nat -d> valO)) ;
  #[local] inf_spsc_queue_G_consumer_G :: AuthExclG Σ (listO valO * listO valO) ;
  #[local] inf_spsc_queue_G_model_G :: AuthExclG Σ (listO valO) ;
  #[local] inf_spsc_queue_G_hist_G :: MonoListG Σ val ;
}.

Definition inf_spsc_queue_Σ := #[
  auth_excl_Σ (natO * (nat -d> valO)) ;
  auth_excl_Σ (listO valO * listO valO) ;
  auth_excl_Σ (listO valO) ;
  mono_list_Σ val
].
Lemma subG_inf_spsc_queue_Σ Σ `{!heapGS Σ} array :
  subG inf_spsc_queue_Σ Σ →
  InfSpscQueueG Σ array.
Proof.
  solve_inG.
Qed.

Section inf_spsc_queue_G.
  Context `{!heapGS Σ} {array} `{inf_spsc_queue_G : !InfSpscQueueG Σ array}.

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

  Definition inf_spsc_queue_make : val :=
    λ: <>,
      record3_make #0 #0 (array.(inf_array_make) #()).

  Definition inf_spsc_queue_push : val :=
    λ: "t" "v",
      let: "back" := !"t".(back) in
      array.(inf_array_set) !"t".(data) "back" "v" ;;
      "t".(back) <- "back" + #1.

  Definition inf_spsc_queue_pop : val :=
    λ: "t",
      let: "front" := !"t".(front) in
      if: "front" = !"t".(back) then (
        NONE
      ) else (
        let: "v" := array.(inf_array_get) !"t".(data) "front" in
        "t".(front) <- "front" + #1 ;;
        array.(inf_array_set) !"t".(data) "front" #() ;;
        SOME "v"
      ).

  Record inf_spsc_queue_name := {
    inf_spsc_queue_name_data : array.(inf_array_name) ;
    inf_spsc_queue_name_producer : gname ;
    inf_spsc_queue_name_consumer : gname ;
    inf_spsc_queue_name_model : gname ;
    inf_spsc_queue_name_hist : gname ;
  }.

  #[local] Instance inf_spsc_queue_name_eq_dec :
    EqDecision inf_spsc_queue_name.
  Proof.
    solve_decision.
  Qed.
  #[local] Instance inf_chaselev_deque_name_countable :
    Countable inf_spsc_queue_name.
  Proof.
    pose encode γ := (
      γ.(inf_spsc_queue_name_data),
      γ.(inf_spsc_queue_name_producer),
      γ.(inf_spsc_queue_name_consumer),
      γ.(inf_spsc_queue_name_model),
      γ.(inf_spsc_queue_name_hist)
    ).
    pose decode := λ '(γ_data, γ_producer, γ_consumer, γ_model, γ_hist), {|
      inf_spsc_queue_name_data := γ_data ;
      inf_spsc_queue_name_producer := γ_producer ;
      inf_spsc_queue_name_consumer := γ_consumer ;
      inf_spsc_queue_name_model := γ_model ;
      inf_spsc_queue_name_hist := γ_hist ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  Notation inf_spsc_queue_namespace_data ι := (ι .@ "data").
  Notation inf_spsc_queue_namespace_inv ι := (ι .@ "inv").

  Implicit Types front back : nat.
  Implicit Types l : loc.
  Implicit Types v t data : val.
  Implicit Types γ : inf_spsc_queue_name.
  Implicit Types waste hist model : list val.
  Implicit Types priv : nat → val.

  #[local] Definition inf_spsc_queue_producer₁' γ_producer back priv :=
    auth_excl_auth (auth_excl_G := inf_spsc_queue_G_producer_G) γ_producer (DfracOwn 1) (back, priv).
  #[local] Definition inf_spsc_queue_producer₁ γ back priv :=
    inf_spsc_queue_producer₁' γ.(inf_spsc_queue_name_producer) back priv.
  #[local] Definition inf_spsc_queue_producer₂' γ_producer back priv :=
    auth_excl_frag (auth_excl_G := inf_spsc_queue_G_producer_G) γ_producer (back, priv).
  #[local] Definition inf_spsc_queue_producer₂ γ back priv :=
    inf_spsc_queue_producer₂' γ.(inf_spsc_queue_name_producer) back priv.
  Definition inf_spsc_queue_producer t : iProp Σ :=
    ∃ l γ back priv,
    ⌜t = #l⌝ ∗
    (* metadata *)
    meta l nroot γ ∗
    (* producer token controlling back field and private values*)
    inf_spsc_queue_producer₁ γ back priv.

  #[local] Definition inf_spsc_queue_consumer₁' γ_consumer hist waste :=
    auth_excl_auth (auth_excl_G := inf_spsc_queue_G_consumer_G) γ_consumer (DfracOwn 1) (hist, waste).
  #[local] Definition inf_spsc_queue_consumer₁ γ hist waste :=
    inf_spsc_queue_consumer₁' γ.(inf_spsc_queue_name_consumer) hist waste.
  #[local] Definition inf_spsc_queue_consumer₂' γ_consumer hist waste :=
    auth_excl_frag (auth_excl_G := inf_spsc_queue_G_consumer_G) γ_consumer (hist, waste).
  #[local] Definition inf_spsc_queue_consumer₂ γ hist waste :=
    inf_spsc_queue_consumer₂' γ.(inf_spsc_queue_name_consumer) hist waste.
  Definition inf_spsc_queue_consumer t : iProp Σ :=
    ∃ l γ hist,
    ⌜t = #l⌝ ∗
    (* metadata *)
    meta l nroot γ ∗
    (* front field *)
    l.(front) ↦ #(length hist) ∗
    (* consumer token controlling history values and wasted values *)
    inf_spsc_queue_consumer₁ γ hist (replicate (length hist) #()).

  #[local] Definition inf_spsc_queue_model₁' γ_model model :=
    auth_excl_auth (auth_excl_G := inf_spsc_queue_G_model_G) γ_model (DfracOwn 1) model.
  #[local] Definition inf_spsc_queue_model₁ γ model :=
    inf_spsc_queue_model₁' γ.(inf_spsc_queue_name_model) model.
  #[local] Definition inf_spsc_queue_model₂' γ_model model :=
    auth_excl_frag (auth_excl_G := inf_spsc_queue_G_model_G) γ_model model.
  #[local] Definition inf_spsc_queue_model₂ γ model :=
    inf_spsc_queue_model₂' γ.(inf_spsc_queue_name_model) model.
  Definition inf_spsc_queue_model t model : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    (* metadata *)
    meta l nroot γ ∗
    (* model values *)
    inf_spsc_queue_model₁ γ model.

  #[local] Definition inf_spsc_queue_hist_auth' γ_hist hist :=
    mono_list_auth γ_hist 1 hist.
  #[local] Definition inf_spsc_queue_hist_auth γ hist :=
    inf_spsc_queue_hist_auth' γ.(inf_spsc_queue_name_hist) hist.
  #[local] Definition inf_spsc_queue_hist_mapsto γ i v :=
    mono_list_mapsto γ.(inf_spsc_queue_name_hist) i v.

  #[local] Definition inf_spsc_queue_inv_inner l γ data : iProp Σ :=
    ∃ back hist waste model priv,
    ⌜back = (length waste + length model)%nat⌝ ∗
    (* back field *)
    l.(back) ↦ #back ∗
    (* data model *)
    array.(inf_array_model') data γ.(inf_spsc_queue_name_data) (waste ++ reverse model) priv ∗
    (* history values *)
    inf_spsc_queue_hist_auth γ (hist ++ reverse model) ∗
    (* consumer token *)
    inf_spsc_queue_consumer₂ γ hist waste ∗
    (* model values *)
    inf_spsc_queue_model₂ γ model ∗
    (* producer token *)
    inf_spsc_queue_producer₂ γ back priv.
  Definition inf_spsc_queue_inv t ι : iProp Σ :=
    ∃ l γ data,
    ⌜t = #l⌝ ∗
    (* metadata *)
    meta l nroot γ ∗
    (* immutable data field *)
    l.(data) ↦□ data ∗
    (* invariants *)
    array.(inf_array_inv) data γ.(inf_spsc_queue_name_data) (inf_spsc_queue_namespace_data ι) ∗
    inv (inf_spsc_queue_namespace_inv ι) (inf_spsc_queue_inv_inner l γ data).

  #[global] Instance inf_spsc_queue_inv_persistent t ι :
    Persistent (inf_spsc_queue_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_spsc_queue_model_timeless t vs :
    Timeless (inf_spsc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_spsc_queue_producer_timeless t :
    Timeless (inf_spsc_queue_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_spsc_queue_consumer_timeless t :
    Timeless (inf_spsc_queue_consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma inf_spsc_queue_producer_alloc :
    ⊢ |==> ∃ γ_producer,
      inf_spsc_queue_producer₁' γ_producer 0 (λ _, #()) ∗
      inf_spsc_queue_producer₂' γ_producer 0 (λ _, #()).
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma inf_spsc_queue_producer_agree γ back1 priv1 back2 priv2 :
    inf_spsc_queue_producer₁ γ back1 priv1 -∗
    inf_spsc_queue_producer₂ γ back2 priv2 -∗
    ⌜back1 = back2 ∧ priv1 = priv2⌝.
  Proof.
    iIntros "Hproducer₁ Hproducer₂".
    iDestruct (auth_excl_agree with "Hproducer₁ Hproducer₂") as %(? & ?%functional_extensionality).
    done.
  Qed.
  #[local] Lemma inf_spsc_queue_producer_update {γ back1 priv1 back2 priv2} back priv :
    inf_spsc_queue_producer₁ γ back1 priv1 -∗
    inf_spsc_queue_producer₂ γ back2 priv2 ==∗
      inf_spsc_queue_producer₁ γ back priv ∗
      inf_spsc_queue_producer₂ γ back priv.
  Proof.
    apply auth_excl_update'.
  Qed.
  Lemma inf_spsc_queue_producer_exclusive t :
    inf_spsc_queue_producer t -∗
    inf_spsc_queue_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & %back & %priv & % & #Hmeta & Hproducer₁1) (%_l & %_γ & %_back & %_priv & % & #_Hmeta & Hproducer₁2)". simplify.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (auth_excl_auth_exclusive with "Hproducer₁1 Hproducer₁2").
  Qed.

  #[local] Lemma inf_spsc_queue_consumer_alloc :
    ⊢ |==> ∃ γ_consumer,
      inf_spsc_queue_consumer₁' γ_consumer [] [] ∗
      inf_spsc_queue_consumer₂' γ_consumer [] [].
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma inf_spsc_queue_consumer_agree γ hist1 waste1 hist2 waste2 :
    inf_spsc_queue_consumer₁ γ hist1 waste1 -∗
    inf_spsc_queue_consumer₂ γ hist2 waste2 -∗
    ⌜hist1 = hist2 ∧ waste1 = waste2⌝.
  Proof.
    iIntros "Hconsumer₁ Hconsumer₂".
    iDestruct (auth_excl_agree_L (auth_excl_G := inf_spsc_queue_G_consumer_G) with "Hconsumer₁ Hconsumer₂") as %[= -> ->]. done.
  Qed.
  #[local] Lemma inf_spsc_queue_consumer_update {γ hist1 waste1 hist2 waste2} hist waste :
    inf_spsc_queue_consumer₁ γ hist1 waste1 -∗
    inf_spsc_queue_consumer₂ γ hist2 waste2 ==∗
      inf_spsc_queue_consumer₁ γ hist waste ∗
      inf_spsc_queue_consumer₂ γ hist waste.
  Proof.
    apply auth_excl_update'.
  Qed.
  Lemma inf_spsc_queue_consumer_exclusive t :
    inf_spsc_queue_consumer t -∗
    inf_spsc_queue_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & %hist & -> & #Hmeta & _ & Hconsumer₁1) (%_l & %_γ & %_hist & %Heq & #_Hmeta & _ & Hconsumer₁2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (auth_excl_auth_exclusive with "Hconsumer₁1 Hconsumer₁2").
  Qed.

  #[local] Lemma inf_spsc_queue_model_alloc :
    ⊢ |==> ∃ γ_model,
      inf_spsc_queue_model₁' γ_model [] ∗
      inf_spsc_queue_model₂' γ_model [].
  Proof.
    apply auth_excl_alloc'.
  Qed.
  #[local] Lemma inf_spsc_queue_model_agree γ model1 model2 :
    inf_spsc_queue_model₁ γ model1 -∗
    inf_spsc_queue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    eauto using auth_excl_agree_L.
  Qed.
  #[local] Lemma inf_spsc_queue_model_update {γ model1 model2} model :
    inf_spsc_queue_model₁ γ model1 -∗
    inf_spsc_queue_model₂ γ model2 ==∗
      inf_spsc_queue_model₁ γ model ∗
      inf_spsc_queue_model₂ γ model.
  Proof.
    apply auth_excl_update'.
  Qed.

  #[local] Lemma inf_spsc_queue_hist_alloc :
    ⊢ |==> ∃ γ_hist,
      inf_spsc_queue_hist_auth' γ_hist [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma inf_spsc_queue_hist_mapsto_get {γ hist} i v :
    hist !! i = Some v →
    inf_spsc_queue_hist_auth γ hist -∗
    inf_spsc_queue_hist_mapsto γ i v.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_mapsto_get.
  Qed.
  #[local] Lemma inf_spsc_queue_hist_agree γ hist i v :
    inf_spsc_queue_hist_auth γ hist -∗
    inf_spsc_queue_hist_mapsto γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_auth_mapsto_lookup.
  Qed.
  #[local] Lemma inf_spsc_queue_hist_update {γ hist} v :
    inf_spsc_queue_hist_auth γ hist ==∗
    inf_spsc_queue_hist_auth γ (hist ++ [v]).
  Proof.
    apply mono_list_auth_update_app.
  Qed.

  Lemma inf_spsc_queue_make_spec ι :
    {{{ True }}}
      inf_spsc_queue_make #()
    {{{ t,
      RET t;
      inf_spsc_queue_inv t ι ∗
      inf_spsc_queue_model t [] ∗
      inf_spsc_queue_producer t ∗
      inf_spsc_queue_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    (* → [array.(inf_array_make) #()] *)
    wp_apply (inf_array_make_spec with "[//]"). iIntros "%data %γ_data (#Hinv_data & Hmodel_data)".

    (* → [record3_make #0 #0 data] *)
    iApply wp_fupd.
    wp_apply (record3_make_spec with "[//]"). iIntros "%l (Hl & Hmeta)".
    iDestruct (record3_model_eq_1 with "Hl") as "(Hfront & Hback & Hdata)".
    iMod (mapsto_persist with "Hdata") as "#Hdata".

    iApply "HΦ".

    iMod inf_spsc_queue_producer_alloc as "(%γ_producer & Hproducer₁ & Hproducer₂)".
    iMod inf_spsc_queue_consumer_alloc as "(%γ_consumer & Hconsumer₁ & Hconsumer₂)".
    iMod inf_spsc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod inf_spsc_queue_hist_alloc as "(%γ_hist & Hhist_auth)".

    set γ := {|
      inf_spsc_queue_name_data := γ_data ;
      inf_spsc_queue_name_producer := γ_producer ;
      inf_spsc_queue_name_consumer := γ_consumer ;
      inf_spsc_queue_name_model := γ_model ;
      inf_spsc_queue_name_hist := γ_hist ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iSplitR "Hfront Hproducer₁ Hconsumer₁ Hmodel₁".
    { iExists l, γ, data. iFrame "#∗". iSplitR; first done.
      iApply inv_alloc. iExists 0, [], [], [], (λ _, #()). auto with iFrame.
    }
    iSplitL "Hmodel₁".
    { iExists l, γ. naive_solver. }
    iSplitL "Hproducer₁".
    { iExists l, γ, 0, (λ _, #()). naive_solver. }
    iExists l, γ, []. auto with iFrame.
  Qed.

  Lemma inf_spsc_queue_push_spec t ι v :
    <<<
      inf_spsc_queue_inv t ι ∗
      inf_spsc_queue_producer t
    | ∀∀ model, inf_spsc_queue_model t model
    >>>
      inf_spsc_queue_push t v @ ↑ι
    <<<
      inf_spsc_queue_model t (v :: model)
    | RET #();
      inf_spsc_queue_producer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv_data & #Hinv) & (%_l & %_γ & %back & %priv & %Heq & #_Hmeta & Hproducer₁)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%_back & %hist & %waste & %model & %_priv & >%Hback & Hback & Hmodel_data & Hhist_auth & Hconsumer₂ & Hmodel₂ & >Hproducer₂)".
    iDestruct (inf_spsc_queue_producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    (* do load *)
    wp_load.
    (* close invariant *)
    iModIntro. iSplitR "Hproducer₁ HΦ".
    { repeat iExists _. auto with iFrame. }
    clear.

    wp_pures.

    (* → [!#l.(data)] *)
    wp_load.

    (* → [array.(inf_array_set) data #back v] *)
    awp_apply (inf_array_set_spec' with "Hinv_data"); first lia.
    (* open invariant *)
    iInv "Hinv" as "(%_back & %hist & %waste & %model & %_priv & >%Hback & Hback & >Hmodel_data & Hhist_auth & Hconsumer₂ & Hmodel₂ & >Hproducer₂)".
    iDestruct (inf_spsc_queue_producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    iAaccIntro with "Hmodel_data"; iIntros "Hmodel_data".
    { iModIntro. iFrame. repeat iExists _. auto with iFrame. }
    (* update private values *)
    set priv' := <[0 := v]> priv.
    iMod (inf_spsc_queue_producer_update back priv' with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    (* close invariant *)
    iModIntro. iSplitR "Hproducer₁ HΦ".
    { iExists back, hist, waste, model, priv'. iFrame. iSplit; first done.
      rewrite Nat2Z.id app_length reverse_length decide_False; last lia.
      rewrite Hback Nat.sub_diag //.
    }
    iIntros "_".
    clear.

    wp_pures.

    (* → [#l.(back) <- #(back + 1)] *)
    (* open invariant *)
    iInv "Hinv" as "(%_back & %hist & %waste & %model & %_priv & >%Hback & Hback & Hmodel_data & Hhist_auth & Hconsumer₂ & Hmodel₂ & >Hproducer₂)".
    iDestruct (inf_spsc_queue_producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    (* do store *)
    wp_store.
    (* update producer tokens *)
    set model'' := v :: model.
    set (priv'' i := priv (S i)).
    iMod (inf_spsc_queue_producer_update (back + 1) priv'' with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    (* begin transaction *)
    iMod "HΦ" as "(%_model & (%_l & %_γ_model & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (inf_spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
    (* update model values *)
    iMod (inf_spsc_queue_model_update model'' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    (* update history values *)
    iMod (inf_spsc_queue_hist_update v with "Hhist_auth") as "Hback_auth".
    (* end transaction *)
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
    { repeat iExists _. auto with iFrame. }
    (* close invariant *)
    iModIntro. iSplitR "Hproducer₁ HΦ".
    { iExists (back + 1), hist, waste, model'', priv''.
      assert (back + 1 = (back + 1)%nat)%Z as -> by lia. iFrame.
      iSplit; first (simpl; auto with lia).
      rewrite reverse_cons !assoc. iFrame.
      iApply (inf_array_model'_shift_l with "Hmodel_data"). intros []; done.
    }
    clear.

    iApply "HΦ". repeat iExists _. auto with iFrame.
  Qed.

  Lemma inf_spsc_queue_pop_spec t ι :
    <<<
      inf_spsc_queue_inv t ι ∗
      inf_spsc_queue_consumer t
    | ∀∀ model, inf_spsc_queue_model t model
    >>>
      inf_spsc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜model = []⌝ ∗
          inf_spsc_queue_model t []
      | Some v =>
          ∃ model',
          ⌜model = model' ++ [v]⌝ ∗
          inf_spsc_queue_model t model'
      end
    | RET o;
      inf_spsc_queue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv_data & #Hinv) & (%_l & %_γ & %hist & %Heq & #_Hmeta & Hfront & Hconsumer₁)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_pures.

    (* → [!#l.(front)] *)
    wp_load.

    wp_pures.

    (* → [!#l.(back)] *)
    wp_bind (!#l.(back))%E.
    (* open invariant *)
    iInv "Hinv" as "(%back & %_hist & %waste & %model & %priv & >%Hback & Hback & Hmodel_data & Hhist_auth & >Hconsumer₂ & Hmodel₂ & Hproducer₂)".
    iDestruct (inf_spsc_queue_consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    (* do load *)
    wp_load.
    rewrite replicate_length in Hback.
    (* branching: is the queue empty? *)
    destruct (decide (back = length hist)) as [-> | Hbranch].

    (* branch 1: empty queue *)
    - destruct (nil_or_length_pos model) as [-> |]; last lia.
      (* begin transaction *)
      iMod "HΦ" as "(%_model & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      (* end transaction *)
      iMod ("HΦ" $! None with "[Hmodel₁]") as "HΦ".
      { iSplit; first done. repeat iExists _. auto. }
      (* close invariant *)
      iModIntro. iSplitR "Hfront Hconsumer₁ HΦ".
      { repeat iExists _. iFrame. rewrite replicate_length //. }
      clear.

      wp_pures. rewrite bool_decide_eq_true_2; last done. wp_pures.

      iApply "HΦ". repeat iExists _. auto with iFrame.

    (* branch 2: non-empty queue *)
    - rename model into _model. destruct (rev_elim _model) as [-> | (model & v & ->)]; first naive_solver.
      (* emit history fragment *)
      iDestruct (inf_spsc_queue_hist_mapsto_get (length hist) v with "Hhist_auth") as "#Hhist_mapsto".
      { rewrite lookup_app_r // Nat.sub_diag reverse_snoc //. }
      (* close invariant *)
      iModIntro. iSplitR "Hfront Hconsumer₁ HΦ".
      { repeat iExists _. iFrame. rewrite replicate_length //. }
      clear- Hbranch.

      wp_pures. rewrite bool_decide_eq_false_2; last naive_solver lia. clear. wp_pures.

      (* → [!#l.(data)] *)
      wp_load.

      (* → [array.(inf_array_get) data #(length hist)] *)
      awp_apply (inf_array_get_spec' with "Hinv_data"); first lia.
      (* open invariant *)
      iInv "Hinv" as "(%back & %_hist & %waste & %model & %priv & >%Hback & Hback & >Hmodel_data & >Hhist_auth & >Hconsumer₂ & Hmodel₂ & Hproducer₂)".
      iDestruct (inf_spsc_queue_consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
      iAaccIntro with "Hmodel_data"; iIntros "Hmodel_data".
      { iModIntro. iFrame. repeat iExists _. auto with iFrame. }
      (* exploit history fragment *)
      iDestruct (inf_spsc_queue_hist_agree with "Hhist_auth Hhist_mapsto") as %Hlookup.
      rewrite lookup_app_r // Nat.sub_diag in Hlookup.
      (* close invariant *)
      iModIntro. iSplitR "Hfront Hconsumer₁ HΦ".
      { repeat iExists _. auto with iFrame. }
      iIntros "_".
      destruct (reverse model) as [| _v rev_model]; simplify.
      rewrite Nat2Z.id app_length replicate_length decide_True; last naive_solver lia.
      rewrite lookup_total_app_r replicate_length // Nat.sub_diag /=.
      clear.

      wp_pures.

      (* → [#l.(front) <- #(length hist + 1)] *)
      wp_bind (#l.(front) <- #(length hist + 1))%E.
      (* open invariant *)
      iInv "Hinv" as "(%back & %_hist & %waste & %model & %priv & >%Hback & Hback & Hmodel_data & Hhist_auth & >Hconsumer₂ & Hmodel₂ & Hproducer₂)".
      iDestruct (inf_spsc_queue_consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
      (* do store *)
      wp_store.
      (* exploit history fragment *)
      iDestruct (inf_spsc_queue_hist_agree with "Hhist_auth Hhist_mapsto") as %Hlookup.
      rewrite lookup_app_r // Nat.sub_diag in Hlookup.
      destruct (reverse model) as [| _v rev_model] eqn:Hrev_model; simplify.
      apply (f_equal reverse) in Hrev_model. rewrite reverse_involutive in Hrev_model. subst.
      (* begin transaction *)
      iMod "HΦ" as "(%_model & (%_l & %_γ_model & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_spsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      (* update model values *)
      iMod (inf_spsc_queue_model_update (reverse rev_model) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      (* end transaction *)
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ".
      { repeat iExists _. iSplit; first rewrite reverse_cons //.
        repeat iExists _. auto.
      }
      (* update consumer tokens *)
      set hist' := hist ++ [v].
      set waste' := replicate (length hist) #() ++ [v].
      iMod (inf_spsc_queue_consumer_update hist' waste' with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
      (* close invariant *)
      iModIntro. iSplitR "Hfront Hconsumer₁ HΦ".
      { repeat iExists _. iFrame.
        iSplit. { rewrite app_length replicate_length !reverse_length -assoc //. }
        rewrite reverse_involutive -!assoc. iFrame.
      }
      clear.

      wp_pures.

      (* → [!#l.(data)] *)
      wp_load.

      (* → [array.(inf_array_set) data #(length hist) #()] *)
      awp_apply (inf_array_set_spec' with "[//]"); first lia.
      (* open invariant *)
      iInv "Hinv" as "(%back & %_hist & %waste & %model & %priv & >%Hback & Hback & >Hmodel_data & Hhist_auth & >Hconsumer₂ & Hmodel₂ & Hproducer₂)".
      iDestruct (inf_spsc_queue_consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
      iAaccIntro with "Hmodel_data"; iIntros "Hmodel_data".
      { iModIntro. iFrame. repeat iExists _. auto with iFrame. }
      (* update consumer tokens *)
      set waste'' := replicate (S (length hist)) #().
      iMod (inf_spsc_queue_consumer_update hist' waste'' with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
      (* close invariant *)
      iModIntro. iSplitR "Hfront Hconsumer₁ HΦ".
      { repeat iExists _. iFrame.
        rewrite Hback /waste' /waste'' Nat2Z.id !app_length !reverse_length !replicate_length Nat.add_1_r /=.
        iSplit; first done.
        rewrite decide_True; last lia.
        rewrite insert_app_l; last first.
        { rewrite app_length replicate_length /=. lia. }
        rewrite insert_app_r_alt; last first.
        { rewrite replicate_length //. }
        rewrite replicate_length Nat.sub_diag -replicate_cons_app //.
      }
      iIntros "_".
      clear.

      wp_pures.

      iApply "HΦ". iExists l, γ, hist'. iFrame "#∗". iSplitR; first done.
      rewrite app_length Z.add_1_r -Nat2Z.inj_succ Nat.add_1_r. auto with iFrame.
  Qed.

  Lemma inf_spsc_queue_unboxed t ι :
    inf_spsc_queue_inv t ι -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ & %data & -> & #Hmeta & #Hdata & #Hinv)". done.
  Qed.

  Program Definition inf_spsc_queue : spsc_queue Σ true := {|
    spsc_queue_make :=
      inf_spsc_queue_make ;
    spsc_queue_push :=
      inf_spsc_queue_push ;
    spsc_queue_pop :=
      inf_spsc_queue_pop ;

    spsc_queue_name :=
      unit ;
    spsc_queue_inv t _ ι :=
      inf_spsc_queue_inv t ι ;
    spsc_queue_model t _ model :=
      inf_spsc_queue_model t model ;
    spsc_queue_producer t _ :=
      inf_spsc_queue_producer t ;
    spsc_queue_consumer t _ :=
      inf_spsc_queue_consumer t ;
  |}.
  Next Obligation.
    simpl. eauto using inf_spsc_queue_producer_exclusive.
  Qed.
  Next Obligation.
    simpl. eauto using inf_spsc_queue_consumer_exclusive.
  Qed.
  Next Obligation.
    iIntros "/= * _ HΦ".
    wp_apply (inf_spsc_queue_make_spec with "[//]"). iIntros "%t".
    iApply ("HΦ" $! t ()).
  Qed.
  Next Obligation.
    eauto using inf_spsc_queue_push_spec.
  Qed.
  Next Obligation.
    eauto using inf_spsc_queue_pop_spec.
  Qed.
  Next Obligation.
    simpl. eauto using inf_spsc_queue_unboxed.
  Qed.
End inf_spsc_queue_G.

#[global] Opaque inf_spsc_queue_make.
#[global] Opaque inf_spsc_queue_push.
#[global] Opaque inf_spsc_queue_pop.

#[global] Opaque inf_spsc_queue_inv.
#[global] Opaque inf_spsc_queue_model.
#[global] Opaque inf_spsc_queue_producer.
#[global] Opaque inf_spsc_queue_consumer.
