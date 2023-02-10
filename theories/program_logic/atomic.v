From iris.bi Require Import
  telescopes.
From iris.bi.lib Require Export
  atomic.
From iris.base_logic Require Import
  invariants.
From iris.program_logic Require Export
  weakestpre.
From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.

Definition atomic_wp `{!irisGS Λ Σ} {TA TB : tele}
  (e : expr Λ)
  (E : coPset)
  (α : TA → iProp Σ)
  (β : TA → TB → iProp Σ)
  (Φ : TA → TB → iProp Σ)
  (f : TA → TB → val Λ)
  : iProp Σ :=
    ∀ Ψ,
    atomic_update (⊤ ∖ E) ∅ α β (λ.. x y, Φ x y -∗ Ψ (f x y)) -∗
    WP e {{ Ψ }}.

Section lemmas.
  Context `{!irisGS Λ Σ} {TA TB : tele}.
  Implicit Types α : TA → iProp Σ.
  Implicit Types β Φ : TA → TB → iProp Σ.
  Implicit Types f : TA → TB → val Λ.

  Lemma atomic_wp_seq e E α β Φ f :
    atomic_wp e E α β Φ f -∗
    ∀ Ψ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ x y -∗ Ψ (f x y)) -∗ WP e {{ Ψ }}.
  Proof.
    iIntros "Hawp %Ψ %x Hα HΨ".
    iApply (wp_frame_wand with "HΨ"). iApply "Hawp".
    iAuIntro. iAaccIntro with "Hα"; first auto. iIntros "%y Hβ !>".
    rewrite !tele_app_bind. iIntros "HΦ HΨ". iApply ("HΨ" with "Hβ HΦ").
  Qed.

  Lemma atomic_wp_inv e E α β Φ f N I :
    ↑ N ⊆ E →
    atomic_wp e (E ∖ ↑ N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) Φ f -∗
    inv N I -∗
    atomic_wp e E α β Φ f.
  Proof.
    iIntros "% Hawp #Hinv %Ψ HΨ".
    iApply "Hawp". iAuIntro.
    iInv "Hinv" as "HI". iApply (aacc_aupd with "HΨ"); first solve_ndisj.
    iIntros "%x Hα". iAaccIntro with "[HI Hα]"; rewrite !tele_app_bind; first by iFrame.
    - iIntros "(HI & $)". auto with iFrame.
    - iIntros "%y". rewrite !tele_app_bind. iIntros "(HI & Hβ)". iRight.
      iExists y. rewrite !tele_app_bind. auto with iFrame.
  Qed.
End lemmas.

Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e @ E '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)
( at level 20,
  α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1 .. xn ,   '/  ' '[' α ']'   '/' '>>' ']'   '/  ' e   '/  ' @  E   '/' '[' '<<'  ∃∃ y1 .. yn ,   '/  ' '[' β  |   '/' RET v ;  Q ']'   '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e @ E '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)
( at level 20,
  α, e, E, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'   '/  ' '[' α ']'   '/' '>>' ']'   '/  ' e   '/  ' @  E   '/' '[' '<<'  ∃∃ y1 .. yn ,   '/  ' '[' β  |   '/' RET v ;  Q ']'   '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e @ E '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e
    E
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)
( at level 20,
  α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1 .. xn ,  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e @ E '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleO)
    e
    E
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)
( at level 20,
  α, e, E, β, v, Q at level 200,
  format "'[hv' '[' 'AWP'  '<<'  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.

Definition atomic_triple `{!irisGS Λ Σ} {TA TB : tele}
  (e : expr Λ)
  (E : coPset)
  (P : iProp Σ)
  (α : TA → iProp Σ)
  (β : TA → TB → iProp Σ)
  (Φ : TA → TB → iProp Σ)
  (f : TA → TB → val Λ)
  : iProp Σ :=
    □ (
      ∀ Ψ,
      P -∗
      atomic_update (⊤ ∖ E) ∅ α β (λ.. x y, Φ x y -∗ Ψ (f x y)) -∗
      WP e {{ Ψ }}
    ).

Section lemmas.
  Context `{!irisGS Λ Σ} {TA TB : tele}.
  Implicit Types α : TA → iProp Σ.
  Implicit Types β Φ : TA → TB → iProp Σ.
  Implicit Types f : TA → TB → val Λ.

  Lemma atomic_triple_seq e E P α β Φ f :
    atomic_triple e E P α β Φ f -∗
    □ ∀ Ψ, P -∗ ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ x y -∗ Ψ (f x y)) -∗ WP e {{ Ψ }}.
  Proof.
    iIntros "#Hatriple !> %Ψ HP %x Hα HΨ".
    iApply (wp_frame_wand with "HΨ"). iApply ("Hatriple" with "HP").
    iAuIntro. iAaccIntro with "Hα"; first auto. iIntros "%y Hβ !>".
    rewrite !tele_app_bind. iIntros "HΦ HΨ". iApply ("HΨ" with "Hβ HΦ").
  Qed.

  Lemma atomic_triple_inv e E P α β Φ f N I :
    ↑ N ⊆ E →
    atomic_triple e (E ∖ ↑ N) P (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) Φ f -∗
    inv N I -∗
    atomic_triple e E P α β Φ f.
  Proof.
    iIntros "% #Hatriple #Hinv !> %Ψ HP HΨ".
    iApply ("Hatriple" with "HP"). iAuIntro.
    iInv "Hinv" as "HI". iApply (aacc_aupd with "HΨ"); first solve_ndisj.
    iIntros "%x Hα". iAaccIntro with "[HI Hα]"; rewrite !tele_app_bind; first by iFrame.
    - iIntros "(HI & $)". auto with iFrame.
    - iIntros "%y". rewrite !tele_app_bind. iIntros "(HI & Hβ)". iRight.
      iExists y. rewrite !tele_app_bind. auto with iFrame.
  Qed.
End lemmas.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    P
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)
( at level 20,
  P, α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' '[' '<<<'  '/  ' '[' P  |  '/' ∀∀  x1 .. xn ,  α ']'  '/' '>>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<<'  ∃∃  y1 .. yn ,  '/  ' '[' β  |  '/' 'RET'  v ;  Q ']'  '/' '>>>' ']' ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    P
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)
( at level 20,
  P, α, e, E, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' '[' '<<<'  '/  ' '[' P  |  '/' α ']'  '/' '>>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<<'  ∃∃  y1 .. yn ,  '/  ' '[' β  |  '/' 'RET'  v ;  Q ']'  '/' '>>>' ']' ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e
    E
    P
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)
( at level 20,
  P, α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' '[' '<<<'  '/  ' '[' P  |  '/' ∀∀  x1 .. xn ,  α ']'  '/' '>>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<<'  '/  ' '[' β  |  '/' 'RET'  v ;  Q ']'  '/' '>>>' ']' ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e
    E
    P
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)
( at level 20,
  P, α, e, E, β, v, Q at level 200,
  format "'[hv' '[' '<<<'  '/  ' '[' P  |  '/' α ']'  '/' '>>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<<'  '/  ' '[' β  |  '/' 'RET'  v ;  Q ']'  '/' '>>>' ']' ']'"
) : bi_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    P
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)
: stdpp_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e
    E
    P
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)
: stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e
    E
    P
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)
: stdpp_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e
    E
    P
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)
: stdpp_scope.
