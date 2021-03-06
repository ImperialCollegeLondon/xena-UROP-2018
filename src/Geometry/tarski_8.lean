import geometry.tarski_7 linear_algebra.basic
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance, priority 0] prop_decidable 


-- Pappus, Pascal and Desargues

theorem thirteen1 {a b c p q r : point} {A : set point} : ¬col a b c → M c p b → M c q a → M a r b → xperp r A (l a b) → perp A (l p q) :=
begin
intros h h1 h2 h3 g1,
have h4 : c ∉ l p q,
  intro h_1,
  suffices : line (l p q),
    apply h (six23.2 ⟨l p q, this, _, _, h_1⟩),
      rw seven6 h2,
      exact (seven24 this (six17b p q)).1 h_1,
    rw seven6 h1,
    exact (seven24 this (six17a p q)).1 h_1,
  apply six14,
  intro h_2,
  subst q,
  exact (six26 h).1 (seven4 h2 h1),
cases exists_of_exists_unique (eight17 (six14 (six26 h4).1) h4) with c' hc,
cases exists_of_exists_unique (eight22 (S q c') (S p c')) with x hx,
cases exists_of_exists_unique (unique_perp x hc.1) with A' hA,
suffices : A = A',
  exact this.symm ▸ hA.2.symm,
apply unique_of_exists_unique (unique_xperp g1.2.1 g1.2.2.2.1) g1.symm,
haveI h5 := (eight14e hA.2).2,
suffices : Sl A' a = b,
  have h6 : a ∉ A',
    intro h_1,
    have h_2 := ten3b h5 h_1,
    exact (six26 h).1 (h_2.symm.trans this),
  have h7 := ten3a h5 h6,
  rw this at *,
  rw M_to_mid h3 at h7,
  exact eight15 h7.2.symm (or.inr (or.inl h3.1.symm)) h7.1,
have h6 : l (S q c') (S p c') = l p q,
  exact (six18 hc.1 (seven18a c' (six13 hc.1).symm) ((seven24 hc.1 (six17b p q)).1 hc.2.2.1) ((seven24 hc.1 (six17a p q)).1 hc.2.2.1)).symm,
have h7 : Sl A' (S q c') = S p c',
  apply (unique_of_Sl h5 _ _ _).symm,
      apply six21b,
          refine ⟨hc.1, h5, eight14a hA.2, _, hA.1⟩,
          rw ←h6,
          exact (or.inr (or.inl hx.1.symm)),
        intro h_1,
        subst x,
        exact (six13 hc.1).symm (seven18 (id_eqd hx.2.symm)),
      rw ←h6,
      simp,
    rw M_to_mid hx,
    exact hA.1,
  rw h6,
  exact hA.2.symm,
have h8 : xperp (S q c') (l a (S q c')) (l (S q c') (S p c')),
  rw [seven6 h2, h6],
  apply (ten18 hc (six17b p q)).symm,
have h9 : xperp (S p c') (l b (S p c')) (l (S q c') (S p c')),
  rw [seven6 h1, h6],
  apply (ten18 hc (six17a p q)).symm,
apply six11a,
  suffices : side (l (S q c') (S p c')) a b,
    apply eleven15b (nine11 this).2.2 (nine11 this).2.2 _ _ _ (side.refla (nine11 this).2.2),
        rw seven6 h1,
        apply eleven16 (seven18a c' (six13 hc.1).symm) (seven9a p (six13 hc.2.1)) (seven18a c' (six13 hc.1).symm) _ _ _,
            rw ←h7,
            intro h_1,
            exact (six13 h8.1) (ten7 h_1),
          rw ←seven6 h1,
          exact (h9.2.2.2.2 (six17a b (S p c')) (six17a _ _)).symm,
        suffices : R (Sl A' (S p c')) (Sl A' (S q c')) (Sl A' a),
          rwa [←h7, ten5, h7] at this,
        apply (ten11d h5).1 (h8.2.2.2.2 (six17a a (S q c')) (six17b _ _)).symm,
      apply side.trans _ this,
      apply side.symm (twelve7.1 (dpar_of_par_neq _ _)).1,
        rw h6,
        apply twelve9 hA.2 (ten3a h5 _).2.symm,
        intro h_1,
        suffices : S q c' = x,
          subst x,
          exact (six13 hc.1).symm (seven18 (id_eqd hx.2.symm)),
        suffices : l a (S q c') = A',
          apply eight14d h8 _,
          rw this,
          refine eight15 _ hA.1 (or.inr (or.inl hx.1.symm)),
          simpa [h6] using hA.2.symm,
        rw ←h6 at *,
        exact unique_of_exists_unique (unique_perp a hc.1) ⟨six17a a (S q c'), S q c', h8.symm⟩ ⟨h_1, hA.2⟩,
      intro h_1,
      exact (nine11 this).2.1 (h_1.symm ▸ six17a a (Sl A' a)),
    exact eqa.refl (six26 (nine11 this).2.2).1 (six26 (nine11 this).2.2).2.1.symm,
  rw [h6, seven6 h2, seven6 h1],
  exact ⟨c, (nine16 (six14 (six26 h4).1) h4 (six17b p q)).symm, (nine16 (six14 (six26 h4).1) h4 (six17a p q)).symm⟩,
apply (ten10 h5 (S p c') (Sl A' a)).trans,
rw [←h7, ten5, ten5, seven6 h2, h7, seven6 h1],
exact (seven13 q c' c).symm.trans (seven13 p c' c)
end

theorem thirteen1a (a : point) {p q : point} : p ≠ q → par (l p q) (l (S p a) (S q a)) :=
begin
intro h,
by_cases h_1 : col p q a,
  exact or.inr ⟨(six14 h), six18 (six14 h) (seven18a a h) 
  ((seven24 (six14 h) (six17a p q)).1 h_1) ((seven24 (six14 h) (six17b p q)).1 h_1)⟩,
cases exists_of_exists_unique (unique_xperp (six14 (seven18a a h)) (or.inr (or.inl (ten1 (S p a) (S q a)).1.symm))) with A ha,
have h1 := thirteen1 _ (seven5 q a) (seven5 p a) (ten1 (S p a) (S q a)) ha.symm,
  rw six17 at h1,
  exact twelve9 h1.symm ⟨mid (S p a) (S q a), ha⟩,
intro h_2,
exact h_1 (six23.2 ⟨l (S p a) (S q a), six14 (seven18a a h), six27 (six14 (seven18a a h)) h_2 (six17a _ _)
(seven5 p a).1, six27 (six14 (seven18a a h)) h_2 (six17b _ _) (seven5 q a).1, h_2⟩)
end

theorem thirteen2a {a b c d: point} {A : set point} : Bl c A d → xperp a A (l c a) → xperp b A (l d b) → ∃ p, B a p b ∧ B c p d :=
begin
intros h h1 h2,
cases h.2.2.2 with p hp,
by_cases h_1 : a = b,
  subst b,
  suffices : p = a,
    subst p,
    exact ⟨a, three1 a a, hp.2⟩,
  refine six21a h.1 (six14 (nine2 h)) _ hp.1 (or.inr (or.inl hp.2.symm)) h1.2.2.1 _,
    intro h_1,
    subst h_1,
    exact h.2.1 (six17a c d),
  suffices : l c a = l d a,
    apply (four11 _).1,
    show d ∈ l c a,
    rw this,
    simp,
  exact unique_of_exists_unique (unique_perp a h.1) ⟨h1.2.2.2.1, a, h1⟩ ⟨h2.2.2.2.1, a, h2⟩,
have h3 := six18 h.1 h_1 h1.2.2.1 h2.2.2.1,
subst h3,
refine ⟨p, _, hp.2⟩,
cases (four11 hp.1).1,
  exact h_2,
exfalso,
rw three2 at h_2,
revert c d,
wlog h3 := h_2 using a b,
  intros,
  cases exists_of_exists_unique (unique_perp p h.1) with P hP,
  suffices : side P c d,
    exact nine9 ⟨(nine11 this).1, (nine11 this).2.1, (nine11 this).2.2, p, hP.1, hp.2⟩ this,
  suffices : side P a b,
    apply side.trans _ (this.trans _),
      apply twelve6 (dpar_of_par_neq (twelve9 hP.2.symm ⟨a, h1.symm⟩) _) (six17a c a) (six17b c a),
      intro h_2,
      subst h_2,
      exact (nine11 this).2.1 (six17b c a),
    apply twelve6 (dpar_of_par_neq (twelve9 hP.2.symm ⟨b, h2.symm⟩) _) (six17b d b) (six17a d b),
    intro h_2,
    subst h_2,
    exact (nine11 this).2.2 (six17b d b),
  suffices : b ≠ p,
    apply (nine12 (eight14e hP.2).2 hP.1 (six7 h3.symm this) _).symm,
    intro h_2,
    exact (eight14a hP.2) (six21 this h.1 (eight14e hP.2).2 (six17b a b) h_2 (or.inl h3) hP.1),
  intro h_2,
  subst p,
  have h4 := six18 h2.2.1 (six26 h.2.1).2.1.symm (or.inl hp.2.symm) (six17b d b),
  rw h4 at *,
  exact h_1 (unique_of_exists_unique (eight18 h.2.1) ⟨six17a a b, a, h1⟩ ⟨six17b a b, b, h2⟩),
rw six17 b a at this,
exact this (ne.symm h_1) h.symm h2 h1 ⟨hp.1, hp.2.symm⟩
end

theorem thirteen2b {a b c d : point} : Bl c (l a b) d → R b c a → R b d a → Bl a (l c d) b :=
begin
intros h h1 h2,
cases exists_of_exists_unique (eight17 h.1 h.2.1) with x hx,
cases exists_of_exists_unique (eight17 h.1 h.2.2.1) with y hy,
have h3 := eleven47 h1.symm hx.symm,
have h4 := eleven47 h2.symm hy.symm,
cases thirteen2a h hx hy with p hp,
have h5 := five7 h3.1 h4.1 hp.1,
have h6 : is p (l a b) (l c d),
  refine ⟨h.1, six14 (nine2 h), _, or.inr (or.inl (h5).symm), or.inr (or.inl hp.2.symm)⟩,
  intro h_1,
  rw h_1 at h,
  exact h.2.1 (six17a c d),
refine ⟨h6.2.1, _, _, p, h6.2.2.2.2, h5⟩,
  intro h_1,
  apply (six21b h6 _ (six17a a b)) h_1,
  intro h_2,
  subst p,
  cases five3 h3.1 h4.1,
    exact h3.2.1 (three4 hp.1 h_2),
  exact h4.2.1 (three4 hp.1.symm h_2),
intro h_1,
apply (six21b h6 _ (six17b a b)) h_1,
intro h_2,
subst p,
cases five3 h3.1.symm h4.1.symm,
  exact h3.2.2 (three4 hp.1 h_2),
exact h4.2.2 (three4 hp.1.symm h_2)
end

theorem thirteen2c {a b c d : point} : Bl c (l a b) d → Bl a (l c d) b → ∃ p, B a p b ∧ B c p d ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c ∧ p ≠ d :=
begin
intros h h1,
cases h.2.2.2 with p hp,
cases h1.2.2.2 with q hq,
have : p = q,
  apply six21a h.1 h1.1 _ hp.1 (or.inr (or.inl hp.2.symm)) (or.inr (or.inl hq.2.symm)) hq.1,
  intro h_1,
  rw h_1 at h,
  exact h.2.1 (six17a c d),
subst q,
refine ⟨p, hq.2, hp.2, _⟩,
repeat {split}; intro h_1; subst p,
      exact h1.2.1 hq.1,
    exact h1.2.2.1 hq.1,
  exact h.2.1 hp.1,
exact h.2.2.1 hp.1
end

theorem thirteen2 {a b c d e : point} : Bl c (l a b) d → R b c a → R b d a → xperp e (l a e) (l c d) → 
eqa b a c d a e ∧ eqa b a d c a e ∧ B c e d :=
begin
intros h h1 h2 h3,
have h4 : side (l a c) b d,
  cases thirteen2c h (thirteen2b h h1 h2) with t ht,
  apply nine15 _ ht.1 ht.2.1,
  intro h_1,
  exact h.2.1 (six23.2 ⟨l a t, six14 ht.2.2.1.symm, six17a a t, or.inl ht.1, (four11 h_1).1⟩),
have h5 : ang_lt c a b c a d,
  cases thirteen2c h (thirteen2b h h1 h2) with t ht,
  suffices : ang_lt c a t c a d,
    exact eleven37 this (eleven9 (six5 (six26 h.2.1).2.2.symm) (six7 ht.1 ht.2.2.1).symm) 
    (eqa.refl (six26 h.2.1).2.2.symm (six26 h.2.2.1).2.2.symm),
  exact eleven32d (four10 (nine11 h4).2.2).2.1 ht.2.2.2.2.2 ht.2.1,
replace h5 := eleven42b h5,
cases eleven32c (λ h_1, (four10 (nine11 h4).2.2).2.2.1 (or.inr (or.inl h_1))) h5 with e' he,
have h6 : side (l a d) e' c,
  suffices : ¬col a d e',
    exact nine12 (six14 (six26 h.2.2.1).2.2) (six17b a d) (six7 he.2.1 (six26 this).2.1.symm) this,
  intro h_1,
  exact (four10 h.2.1).2.2.2.1 (eleven21d (four11 h_1).2.1 he.2.2.symm),
have h7 : eqa b a d e' a c,
  exact eleven22b h4 h6 he.2.2.flip (eleven6 (six26 h.2.1).2.2.symm (six26 h.2.2.1).2.2.symm),
suffices : e = e',
  subst e',
  exact ⟨eleven7 he.2.2, eleven8 h7, he.2.1.symm⟩,
apply unique_of_exists_unique (eight17 h3.2.1 (four10 (nine11 h6).2.2).2.2.2.2) h3.symm _,
refine eight15 _ (or.inr (or.inl he.2.1)) (six17b a e'),
have h8 := (eqd.symm h1.symm).trans h2.symm,
apply (thirteen1 _ (seven5 c b) (seven5 d b) (ten1 (S c b) (S d b)).symm _).symm,
  intro h_1,
  exact (thirteen2b h h1 h2).2.2.1 (six23.2 ⟨l (S d b) (S c b), six14 (seven18a b (nine2 h.symm)), 
  six27 (six14 (seven18a b (nine2 h.symm))) (six17b _ _) h_1 (seven5 c b).1.symm, 
  six27 (six14 (seven18a b (nine2 h.symm))) (six17a _ _) h_1 (seven5 d b).1.symm, h_1⟩),
haveI ha := six14 he.2.2.2.2.2.1.symm,
rw six17 (S d b) (S c b),
suffices : Sl (l a e') (S c b) = S d b,
  rw ←this,
  refine eight15 (ten3a ha _).2 (ten3a ha _).1 (or.inr (or.inl (ten1 (S c b) (Sl (l a e') (S c b))).1.symm));
  intro h_1;
  exact (seven18a b (nine2 h)) (this ▸ (ten3b ha h_1).symm),
suffices : eqa (S c b) a e' (S d b) a e',
  cases eleven15d this.flip (six14 this.2.1),
    exact ((seven18a b (nine2 h)) (six11a h_1 h8)).elim,
  simp only [six17] at h_1,
  apply ten4.1,
  apply six11a h_1.symm,
  simpa [ten3b ha (six17a a e')] using (ten10 ha a (S d b)).symm.trans h8.symm,
suffices : eqa (S c b) a c e' a d,
  apply eleven8 (eleven22a _ _ this _),
      apply ((nine8 (nine10a (nine11 h4).1 (six17b a c) (nine11 h4).2.1)).2 _).symm,
      exact nine19a h4 (six17b a c) (six7 he.2.1.symm he.1).symm,
    apply (nine8 (nine10a (nine11 h6).1 (six17b a d) (four10 h.2.2.1).1)).2 _,
    apply (h6.trans _).symm,
    cases thirteen2c h (thirteen2b h h1 h2) with t ht,
    apply (nine15 _ ht.1 ht.2.1.symm).symm,
    intro h_1,
    exact h.2.2.1 (six23.2 ⟨l a t, six14 ht.2.2.1.symm, six17a a t, or.inl ht.1, (four11 h_1).1⟩),
  apply h7.symm.flip.trans,
  replaceI h6 := (nine11 h6).1,
  suffices : S d b = Sl (l a d) b,
    rw this,
    simpa [ten3b h6 (six17a a d), ten3b h6 (six17b a d)] using eleven12a h6 h7.2.1 h7.1,
  apply unique_of_Sl h6 (four10 h.2.2.1).1 _ (perp_of_R h7.2.1.symm (six26 h.2.2.1).2.1 h2.symm),
  simp [mid_of_S d b, six17b a d],
apply (he.2.2.symm.trans _).symm.flip,
replaceI h4 := (nine11 h4).1,
suffices : S c b = Sl (l a c) b,
  rw this,
  simpa [ten3b h4 (six17a a c), ten3b h4 (six17b a c)] using eleven12a h4 he.2.2.1 h7.1,
apply unique_of_Sl h4 (four10 h.2.1).1 _ (perp_of_R he.2.2.1.symm (six26 h.2.1).2.1 h1.symm),
simp [mid_of_S c b, six17b a c]
end

theorem thirteen7a {α : angle point} {C : dist point} (hα : acute α) (hc : ¬C = 0) (hα1 : ¬α = 0) :
∃ a b c (hab : a ≠ b) (hcb : c ≠ b), ⟦(a, b)⟧ = C ∧ R a c b ∧ α = ⟦⟨(a, b, c), hab, hcb⟩⟧ :=
begin
rcases quotient.exists_rep α with ⟨⟨⟨p, b, q⟩, hpb, hqb⟩, h2⟩,
subst α,
change ang_acute p b q at hα,
have hpbq : ¬col p b q,
  intro h_1,
  exact hα1 (zero_iff_sided.2 (sided_of_acute_col hα h_1)),
rcases thirteen3 hpbq hc with ⟨⟨a, c⟩, h3, h, h4⟩,
have h2 := h4.symm.2.2.2.2 (six17a a c) (six17a b q),
have h5 : sided b q c,
  apply eleven48 (hα.trans (eleven9 h3.symm (six5 hqb))) h4.2.2.1 _ h2,
  dsimp,
  intro h_1,
  subst b,
  apply (eleven45a hα).1 ⟨hpb, hqb, h4.symm.2.2.2.2 (four11 (six4.1 h3).1).2.2.2.2 (six17b c q)⟩,
exact ⟨a, b, c, h3.2.1, h5.2.1, eq.trans (quotient.sound (show (a, b) ≈ (b, a), from eqd_refl a b)) h,
  h2, quotient.sound (eleven9 h3.symm h5.symm)⟩
end

theorem thirteen7b {β : angle point} {a b c : point} (hab : a ≠ b) : ¬col a b c → acute β → β ≠ 0 → ∃ d (hdb : d ≠ b), β = ⟦⟨(a, b, d), hab, hdb⟩⟧ ∧ Bl c (l b a) d ∧ R a d b :=
begin
intros h h1 h2,
rcases quotient.exists_rep β with ⟨⟨⟨p, q, r⟩, h3⟩, h4⟩,
subst β,
change ang_acute p q r at h1,
replace h2 : ¬col p q r,
  intro h_1,
  apply h2 (zero_iff_sided.2 _),
  exact sided_of_acute_col h1 h_1,
cases nine10 (six14 hab) h with t ht,
cases eleven15a h2 ht.2.2.1 with s hs,
cases exists_of_exists_unique (eight17 (six14 hs.1.2.2.2.1.symm) (four10 (nine11 hs.2).2.1).2.2.1) with d hd,
have h3 : sided b s d,
  apply eleven48 (h1.trans hs.1) hd.2.2.1 _ (hd.symm.2.2.2.2 (six17a a d) (six17a b s)),
  intro h_1,
  subst d,
  exact (eleven45a (h1.trans hs.1)).1 ⟨hs.1.2.2.1, hs.1.2.2.2.1, hd.symm.2.2.2.2 (six17a a b) (six17b b s)⟩,
refine ⟨d, h3.2.1, _, _,  hd.symm.2.2.2.2 (six17a a d) (six17a b s)⟩,
  exact quotient.sound (hs.1.trans (eleven9 (six5 hab) h3.symm)),
exact six17 a b ▸ ((nine8 ht.symm).2 (nine19a hs.2.symm (six17b a b) h3)).symm
end

theorem thirteen7c {α β : angle point} {C : dist point} : acute α → acute β → cos α (cos β C) = cos β (cos α C) :=
begin
intros hα hβ,
by_cases hc : C = 0,
  subst C,
  simp [cos_times_zero],
by_cases hα1 : α = 0,
  subst α,
  rw [cos_zero, cos_zero],
by_cases hβ1 : β = 0,
  subst β,
  rw [cos_zero, cos_zero],
rcases thirteen7a hα hc hα1 with ⟨a, b, c, hab, hcb, h, h1, h2⟩,
clear hc,
subst_vars,
change ang_acute a b c at hα,
replace hα1 : ¬col a b c,
  intro h_1,
  apply hα1 (zero_iff_sided.2 _),
  exact sided_of_acute_col hα h_1,
rcases thirteen7b hab hα1 hβ hβ1 with ⟨d, hdb, h2, hd⟩,
subst β,
rw [←thirteen5b hab hcb h1, ←thirteen5b hab hdb hd.2],
have h2 := thirteen2b hd.1 h1 hd.2,
cases exists_of_exists_unique (eight17 h2.1 h2.2.1) with e he,
have h3 := thirteen2 hd.1 h1 hd.2 he.symm,
suffices : cos ⟦⟨(d, b, e), hdb, h3.1.2.2.2.1⟩⟧ ⟦(d, b)⟧ = cos ⟦⟨(c, b, e), hcb, h3.1.2.2.2.1⟩⟧ ⟦(c, b)⟧,
  have h4 : (⟦⟨(a, b, c), hab, hcb⟩⟧ : angle point) = ⟦⟨(d, b, e), hdb, h3.1.2.2.2.1⟩⟧,
    exact quotient.sound h3.1,
  have h5 : (⟦⟨(a, b, d), hab, hdb⟩⟧ : angle point) = ⟦⟨(c, b, e), hcb, h3.1.2.2.2.1⟩⟧,
    exact quotient.sound h3.2.1,
  rwa [h4, h5],
rw [←thirteen5b hdb h3.1.2.2.2.1 _, ←thirteen5b hcb h3.1.2.2.2.1 _],
  exact he.2.2.2.2 (six17a c d) (six17a b e),
exact he.2.2.2.2 (six17b c d) (six17a b e)
end

theorem thirteen7 (α β : angle point) (C : dist point) : cos α (cos β C) = cos β (cos α C) := 
begin
by_cases ha : right α,
  simp [cos_right ha, cos_right ha],
by_cases hb : right β,
  simp [cos_right hb, cos_right hb],
replace ha : acute α ∨ obtuse α,
  simpa [ha] using angle_trichotomy α,
replace hb : acute β ∨ obtuse β,
  simpa [hb] using angle_trichotomy β,
cases ha.symm,
  have h1 := supp_of_obtuse.1 h,
  rw cos_supp α,
all_goals 
{ cases hb.symm,
    have h2 := supp_of_obtuse.1 h_1,
    rw cos_supp β,
  all_goals 
  { apply thirteen7c;
    assumption}}
end

lemma thirteen11a {o a b a' b' : point} : ¬col o a a' → col o a b → col o a' b' → b ≠ o → b' ≠ o →
¬col o a b' ∧ ¬col o b a' :=
begin
sorry
end

lemma thirteen11b {o a b a' b' : point} : ¬col o a b' → ¬col o b a' → par (l a b') (l b a') →
∃ x x', xperp x (l o x) (l a b') ∧ xperp x' (l o x) (l b a') :=
begin
sorry
end

lemma thirteen11c {o a b a' b' x x' : point} : ¬col o a a' → col o a b → col o a' b' → b ≠ o → b' ≠ o → 
par (l a b') (l b a') → xperp x (l o x) (l a b') → xperp x' (l o x) (l b a') → eqa a o x b o x' ∧ eqa a' o x' b' o x :=
begin
sorry
end

lemma thirteen11d {o a b a' b' x x' : point} (h : eqa a o x b o x') (h1 : eqa a' o x' b' o x) : ¬col o a a' →
col o a b → col o a' b' → b ≠ o → b' ≠ o → par (l a b') (l b a') → xperp x (l o x) (l a b') → xperp x' (l o x) (l b a') :=
begin
sorry
end

theorem thirteen11 {o a b c a' b' c' : point} : ¬col o a a' → col o a b → col o a c → b ≠ o → c ≠ o → col o a' b' → 
col o a' c' → b' ≠ o → c' ≠ o → par (l b c') (l c b') → par (l c a') (l a c') → par (l a b') (l b a') :=
begin
intros h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10,
sorry












end

end Euclidean_plane