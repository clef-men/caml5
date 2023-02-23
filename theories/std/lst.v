From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types v t s acc fn : val.
  Implicit Types vs ws : list val.

  Notation NIL := NONEV
  ( only parsing
  ).
  Notation CONS v t := (SOME (v, t))
  ( only parsing
  ).
  Notation CONSV v t := (SOMEV (v, t))
  ( only parsing
  ).

  (* Definition lst_match : val := *)
  (*   λ: "t" "fn_nil" "fn_cons", *)
  (*     match: "t" with *)
  (*       NONE => *)
  (*         "fn_nil" #() *)
  (*     | SOME "p" => *)
  (*         "fn_cons" (Fst "p") (Snd "p") *)
  (*     end. *)
  (* Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' v , t => e2 'end'" := ( *)
  (*   lst_match e0 (λ: <>, e1 #()) (λ: v t, e2) *)
  (* )%E *)
  (* ( e0, e1, v, t, e2 at level 200, *)
  (*   format "'[hv' 'match:'  e0  'with'  '/  ' '[' 'NIL'  =>  '/  ' e1 ']'  '/' '[' |  'CONS'  v ,  t  =>  '/    ' e2 ']'  '/' 'end' ']'" *)
  (* ) : expr_scope. *)
  (* Notation "'match:' e0 'with' 'CONS' v t => e1 | 'NIL' => e2 'end'" := ( *)
  (*   lst_match e0 (λ: <>, e2 #()) (λ: v t, e1) *)
  (* )%E *)
  (* ( e0, e1, v, t, e2 at level 200, *)
  (*   only parsing *)
  (* ) : expr_scope. *)

  Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' v , t => e2 'end'" := (
    match: e0 with
      NONE =>
        e1
    | SOME "__p" =>
        let: v := Fst "__p" in
        let: t := Snd "__p" in
        e2
    end
  )%E
  ( e0, e1, v, t, e2 at level 200,
    only parsing
  ) : expr_scope.
  Notation "'match:' e0 'with' 'CONS' v t => e1 | 'NIL' => e2 'end'" := (
    match: e0 with
      NONE =>
        e2
    | SOME "__p" =>
        let: v := Fst "__p" in
        let: t := Snd "__p" in
        e1
    end
  )%E
  ( e0, v, t, e1, e2 at level 200,
    only parsing
  ) : expr_scope.

  Definition lst_nil : val :=
    NIL.
  Definition lst_cons : val :=
    λ: "v" "t",
      CONS "v" "t".
  Definition lst_singleton : val :=
    λ: "v",
      CONS "v" NIL.

  Definition lst_head : val :=
    λ: "t",
      match: "t" with
        NIL => Fail
      | CONS "v", <> => "v"
      end.
  Definition lst_tail : val :=
    λ: "t",
      match: "t" with
        NIL => Fail
      | CONS <>, "t" => "t"
      end.

  Definition lst_is_empty : val :=
    λ: "t",
      match: "t" with
        NIL => #true
      | CONS <>, <> => #false
      end.

  Definition lst_get : val :=
    rec: "lst_get" "t" "i" :=
      if: "i" = #0 then (
        lst_head "t"
      ) else (
        "lst_get" (lst_tail "t") ("i" - #1)
      ).

  Definition lst_foldl : val :=
    rec: "lst_foldl" "t" "acc" "fn" :=
      match: "t" with
        NIL =>
          "acc"
      | CONS "v", "t" =>
          "lst_foldl" "t" ("fn" "acc" "v") "fn"
      end.

  Definition lst_foldr : val :=
    rec: "lst_foldr" "t" "fn" "acc" :=
      match: "t" with
        NIL =>
          "acc"
        | CONS "v", "t" =>
            "fn" "v" ("lst_foldr" "t" "fn" "acc")
      end.

  Definition lst_size : val :=
    λ: "t",
      lst_foldl "t" #0 (λ: "acc" <>, "acc" + #1).

  Definition lst_rev : val :=
    λ: "t",
      lst_foldl "t" NIL (λ: "acc" "v", CONS "v" "acc").

  Definition lst_app : val :=
    λ: "t1" "t2",
      lst_foldr "t1" lst_cons "t2".
  Definition lst_snoc : val :=
    λ: "t" "v",
      lst_app "t" (lst_singleton "v").

  Definition lst_iter : val :=
    λ: "t" "fn",
      lst_foldl "t" #() (λ: <> "v", "fn" "v").

  Definition lst_map : val :=
    rec: "lst_map" "t" "fn" :=
      match: "t" with
        NIL =>
          NIL
      | CONS "v", "t" =>
          let: "v" := "fn" "v" in
          let: "t" := "lst_map" "t" "fn" in
          CONS "v" "t"
      end.

  Inductive lst_model' : val → list val → Prop :=
    | lst_model'_nil :
        lst_model' NIL []
    | lst_model'_cons v t vs :
        lst_model' t vs →
        lst_model' (CONSV v t) (v :: vs).
  #[local] Hint Constructors lst_model' : core.

  Definition lst_model t vs : iProp Σ :=
    ⌜lst_model' t vs⌝.

  #[global] Instance lst_model_persistent t o :
    Persistent (lst_model t o).
  Proof.
    apply _.
  Qed.
  #[global] Instance lst_model_timeless t o :
    Timeless (lst_model t o).
  Proof.
    apply _.
  Qed.

  (* Lemma wp_lst_match t vs (fn_nil fn_cons : val) Φ : *)
  (*   (vs = [] → ⊢ WP fn_nil #() {{ Φ }}) → *)
  (*   (∀ v t' vs', vs = v :: vs' → lst_model t' vs' -∗ WP fn_cons v t' {{ Φ }}) → *)
  (*   lst_model t vs -∗ WP lst_match t fn_nil fn_cons {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "%Hnil %Hcons %Ht". *)
  (*   wp_rec. wp_pures. destruct vs; invert Ht; wp_pures. *)
  (*   - wp_apply Hnil; first done. *)
  (*   - wp_apply Hcons; done. *)
  (* Qed. *)
  (* Tactic Notation *)
  (*   "wp_lst_match" "as" *)
  (*       simple_intropattern(Hnil) *)
  (*   "|" simple_intropattern(v) *)
  (*       simple_intropattern(t') *)
  (*       simple_intropattern(vs') *)
  (*       simple_intropattern(Hcons) *)
  (* := *)
  (*   iApply wp_lst_match; *)
  (*   [ intros Hnil; wp_finish *)
  (*   | intros v t' vs' Hcons *)
  (*   | try done *)
  (*   ]. *)
  (* Lemma lst_head_spec t vs v vs' : *)
  (*   vs = v :: vs' → *)
  (*   {{{ lst_model t vs }}} *)
  (*     lst_head t *)
  (*   {{{ RET v; True }}}. *)
  (* Proof. *)
  (*   iIntros (->) "%Φ %Ht HΦ". *)
  (*   wp_rec. wp_pures. wp_lst_match as ? | ? ? ? ?; first done. *)
  (*   iIntros "Ht'". *)
  (*   wp_pures. iApply "HΦ". done. *)
  (* Qed. *)

  Lemma lst_nil_spec :
    ⊢ lst_model lst_nil [].
  Proof.
    auto.
  Qed.
  Lemma lst_cons_spec v t vs :
    {{{ lst_model t vs }}}
      lst_cons v t
    {{{ t', RET t'; lst_model t' (v :: vs) }}}.
  Proof.
    iIntros "%Φ" ([]) "HΦ";
      wp_rec; wp_pures; iApply "HΦ"; auto.
  Qed.
  Lemma lst_singleton_spec v :
    {{{ True }}}
      lst_singleton v
    {{{ t, RET t; lst_model t [v] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures. iApply "HΦ". auto.
  Qed.

  Lemma lst_head_spec t vs v vs' :
    vs = v :: vs' →
    {{{ lst_model t vs }}}
      lst_head t
    {{{ RET v; True }}}.
  Proof.
    iIntros (->) "%Φ %Ht HΦ". invert Ht.
    wp_rec. wp_pures. iApply "HΦ". done.
  Qed.
  Lemma lst_tail_spec t vs v vs' :
    vs = v :: vs' →
    {{{ lst_model t vs }}}
      lst_tail t
    {{{ t', RET t'; lst_model t' vs' }}}.
  Proof.
    iIntros (->) "%Φ %Ht HΦ". invert Ht.
    wp_rec. wp_pures. iApply "HΦ". done.
  Qed.

  Lemma lst_is_empty_spec t vs :
    {{{ lst_model t vs }}}
      lst_is_empty t
    {{{ RET #(bool_decide (vs = [])); True }}}.
  Proof.
    iIntros "%Φ" ([]) "HΦ";
      wp_rec; wp_pures; iApply "HΦ"; done.
  Qed.

  Lemma lst_get_spec t vs i :
    (0 ≤ i < length vs)%Z →
    {{{ lst_model t vs }}}
      lst_get t #i
    {{{ v, RET v; ⌜vs !! Z.to_nat i = Some v⌝ }}}.
  Proof.
    rename i into _i. intros ((i & ->)%Z_of_nat_complete & Hi). revert Hi.
    rewrite Nat2Z.id.
    iInduction i as [| i] "IH" forall (t vs).
    all: iIntros "%Hi %Φ %Ht HΦ".
    all: destruct vs as [| v vs]; first done.
    all: wp_rec; wp_pures.
    - wp_apply (lst_head_spec _ _ v vs); [auto.. |]. iIntros "_".
      iApply "HΦ". done.
    - wp_apply lst_tail_spec; [naive_solver.. |]. iIntros "%t' %Ht'".
      assert (S i - 1 = i)%Z as -> by lia.
      wp_apply "IH"; [| eauto |].
      { list_simplifier. iPureIntro. lia. }
      iIntros "%v' %". iApply "HΦ". done.
  Qed.

  #[local] Lemma lst_foldl_spec_strong vs_done Φ t vs acc fn :
    {{{
      lst_model t vs ∗
      Φ vs_done acc ∗
      ∀ acc' v vs' vs'',
      {{{ ⌜vs_done ++ vs = vs' ++ v :: vs''⌝ ∗ Φ vs' acc' }}}
        fn acc' v
      {{{ acc'', RET acc''; Φ (vs' ++ [v]) acc'' }}}
    }}}
      lst_foldl t acc fn
    {{{ acc',
      RET acc';
      Φ (vs_done ++ vs) acc'
    }}}.
  Proof.
    iInduction vs as [| v vs] "IH" forall (vs_done t acc).
    all: iIntros "%Ψ (%Ht & HΦ & #Hfn) HΨ".
    - invert Ht.
      wp_rec. wp_pures.
      iApply "HΨ". list_simplifier. done.
    - inversion_clear Ht as [| ? t' ? Ht']. simplify_eq/=.
      wp_rec. wp_pures.
      wp_apply ("Hfn" with "[$HΦ //]"). iIntros "%acc' HΦ".
      wp_apply ("IH" with "[$HΦ]"); list_simplifier; auto.
  Qed.
  Lemma lst_foldl_spec Φ t vs acc fn :
    {{{
      lst_model t vs ∗
      Φ [] acc ∗
      ∀ acc' v vs' vs'',
      {{{ ⌜vs = vs' ++ v :: vs''⌝ ∗ Φ vs' acc' }}}
        fn acc' v
      {{{ acc'', RET acc''; Φ (vs' ++ [v]) acc'' }}}
    }}}
      lst_foldl t acc fn
    {{{ acc',
      RET acc';
      Φ vs acc'
    }}}.
  Proof.
    pose proof lst_foldl_spec_strong []. list_simplifier. done.
  Qed.

  Lemma lst_foldr_spec Φ t vs acc fn :
    {{{
      lst_model t vs ∗
      Φ acc [] ∗
      ∀ acc' v vs' vs'',
      {{{ ⌜vs = vs'' ++ v :: vs'⌝ ∗ Φ acc' vs' }}}
        fn v acc'
      {{{ acc'', RET acc''; Φ acc'' (v :: vs') }}}
    }}}
      lst_foldr t fn acc
    {{{ acc',
      RET acc';
      Φ acc' vs
    }}}.
  Proof.
    iInduction vs as [| v vs] "IH" forall (t).
    all: iIntros "%Ψ (%Ht & HΦ & #Hfn) HΨ".
    - invert Ht.
      wp_rec. wp_pures.
      iApply "HΨ". list_simplifier. auto.
    - inversion_clear Ht as [| ? t' ? Ht']. simplify_eq/=.
      wp_rec. wp_pures.
      wp_apply ("IH" with "[$HΦ]").
      { iSplit; first done. clear.
        iIntros "%acc' %v' %vs' %vs'' !> %Ψ (%Hv' & HΦ) HΨ".
        wp_apply ("Hfn" with "[$HΦ]"); first rewrite Hv' app_comm_cons; done.
      }
      iIntros "%acc' HΦ".
      wp_apply ("Hfn" with "[$HΦ]"); first erewrite app_nil_l; done.
  Qed.

  Lemma lst_size_spec t vs :
    {{{ lst_model t vs }}}
      lst_size t
    {{{ RET #(length vs); True }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_foldl_spec (λ vs' acc, ⌜acc = #(length vs')⌝)%I with "[$Ht]").
    { iSplit; first done. clear.
      iIntros "%acc %v %vs' %vs'' !> %Φ (% & ->) HΦ".
      wp_rec. wp_pures.
      iApply "HΦ". iPureIntro. repeat f_equal. rewrite app_length /=. lia.
    }
    iIntros "%acc' ->". iApply ("HΦ" with "[//]").
  Qed.

  Lemma lst_rev_spec t vs :
    {{{ lst_model t vs }}}
      lst_rev t
    {{{ t', RET t'; lst_model t' (reverse vs) }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_foldl_spec (λ vs' acc, lst_model acc (reverse vs'))%I with "[$Ht]").
    { iSplit; first done. clear.
      iIntros "%acc %v %vs' %vs'' !> %Φ (% & %Hacc) HΦ".
      wp_rec. wp_pures.
      iApply "HΦ". iPureIntro. rewrite reverse_app /=. auto.
    }
    iIntros "%acc' Hacc'". iApply ("HΦ" with "Hacc'").
  Qed.

  Lemma lst_app_spec t1 vs1 t2 vs2 :
    {{{ lst_model t1 vs1 ∗ lst_model t2 vs2 }}}
      lst_app t1 t2
    {{{ t, RET t; lst_model t (vs1 ++ vs2) }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_foldr_spec (λ acc vs, lst_model acc (vs ++ vs2)) with "[$Ht1]"); last done.
    list_simplifier. iSplit; first done.
    clear. iIntros "%acc %v1 %vs1' %vs1'' !> %Φ (% & #Hacc) HΦ".
    wp_apply (lst_cons_spec with "Hacc"). iIntros "%t Ht".
    iApply ("HΦ" with "Ht").
  Qed.
  Lemma lst_snoc_spec t vs v :
    {{{ lst_model t vs }}}
      lst_snoc t v
    {{{ t', RET t'; lst_model t' (vs ++ [v]) }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_singleton_spec with "[//]"). iIntros "%t_v #Ht_v".
    wp_apply (lst_app_spec t vs t_v [v] with "[$Ht $Ht_v]"). done.
  Qed.

  Lemma lst_iter_spec Φ t vs fn :
    {{{
      lst_model t vs ∗
      Φ [] ∗
      ∀ v vs' vs'',
      {{{ ⌜vs = vs' ++ v :: vs''⌝ ∗ Φ vs' }}}
        fn v
      {{{ RET #(); Φ (vs' ++ [v]) }}}
    }}}
      lst_iter t fn
    {{{ RET #(); Φ vs }}}.
  Proof.
    iIntros "%Ψ (#Ht & HΦ & #Hfn) HΨ".
    wp_rec. wp_pures.
    wp_apply (lst_foldl_spec (λ vs' acc, ⌜acc = #()⌝ ∗ Φ vs')%I with "[$Ht $HΦ]").
    { iSplit; first done.
      clear. iIntros "%acc %v %vs' %vs'' !> %Ψ (% & -> & HΦ) HΨ".
      wp_pures.
      wp_apply ("Hfn" with "[$HΦ //]").
      iIntros "HΦ". iApply "HΨ". naive_solver.
    }
    iIntros "%acc (-> & HΦ)". iApply "HΨ". done.
  Qed.

  #[local] Lemma lst_map_spec_strong vs_done ws_done Φ t vs fn :
    {{{
      lst_model t vs ∗
      Φ vs_done ws_done ∗
      ∀ v vs' vs'' ws',
      {{{ ⌜vs_done ++ vs = vs' ++ v :: vs''⌝ ∗ Φ vs' ws' }}}
        fn v
      {{{ w, RET w; Φ (vs' ++ [v]) (ws' ++ [w]) }}}
    }}}
      lst_map t fn
    {{{ s ws,
      RET s;
      lst_model s ws ∗
      Φ (vs_done ++ vs) (ws_done ++ ws)
    }}}.
  Proof.
    iInduction vs as [| v vs] "IH" forall (vs_done ws_done t).
    all: iIntros "%Ψ (%Ht & HΦ & #Hfn) HΨ".
    - invert Ht.
      wp_rec. wp_pures.
      iApply ("HΨ" $! _ []). list_simplifier. auto.
    - inversion_clear Ht as [| ? t' ? Ht']. simplify_eq/=.
      wp_rec. wp_pures.
      wp_apply ("Hfn" with "[$HΦ //]"). iIntros "%w HΦ".
      wp_pures.
      wp_apply ("IH" with "[$HΦ]").
      { iSplit; first done. list_simplifier. done. }
      iIntros "%s %ws (%Hs & HΦ)".
      wp_pures.
      list_simplifier. iApply ("HΨ" with "[$HΦ]"). naive_solver.
  Qed.
  Lemma lst_map_spec Φ t vs fn :
    {{{
      lst_model t vs ∗
      Φ [] [] ∗
      ∀ v vs' vs'' ws',
      {{{ ⌜vs = vs' ++ v :: vs''⌝ ∗ Φ vs' ws' }}}
        fn v
      {{{ w, RET w; Φ (vs' ++ [v]) (ws' ++ [w]) }}}
    }}}
      lst_map t fn
    {{{ s ws,
      RET s;
      lst_model s ws ∗
      Φ vs ws
    }}}.
  Proof.
    pose proof lst_map_spec_strong [] []. list_simplifier. done.
  Qed.
End heapGS.

#[global] Opaque lst_nil.
#[global] Opaque lst_cons.
#[global] Opaque lst_singleton.
#[global] Opaque lst_head.
#[global] Opaque lst_tail.
#[global] Opaque lst_is_empty.
#[global] Opaque lst_get.
#[global] Opaque lst_foldl.
#[global] Opaque lst_foldr.
#[global] Opaque lst_size.
#[global] Opaque lst_rev.
#[global] Opaque lst_app.
#[global] Opaque lst_snoc.
#[global] Opaque lst_iter.
#[global] Opaque lst_map.

#[global] Typeclasses Opaque lst_model.
