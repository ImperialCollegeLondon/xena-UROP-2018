import geometry.tarski_6
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance] prop_decidable

theorem col_of_perp {a b p q : point} : p ≠ q → R a p q → R b p q → col p a b :=
λ h h1 h2, not_3dim (seven12b h) (seven5 p q).2 h1 h2

theorem coplanar {a : point} (b : point) {A : set point} : line A → a ∉ A → b ∈ pl A a :=
begin
intros h h1,
cases exists_of_exists_unique (eight17 h h1) with p hp,
by_cases h2 : b ∈ A,
  exact or.inr (or.inl h2),
cases ten15 h hp.1 h2 with c hc,
suffices : col p a c,
  by_cases h_1 : B c p a,
    apply (or.inr (or.inr ((nine8 _).2 hc.2).symm)),
    exact ⟨h, (nine11 hc.2).2.1, h1, p, hp.1, h_1⟩,
  apply or.inl (hc.2.symm.trans _),
  exact nine12 h hp.1 (six4.2 ⟨(four11 this).2.2.2.1, h_1⟩) (nine11 hc.2).2.1,
rcases six22 h hp.1 with ⟨q, h3, h4⟩,
subst h4,
apply col_of_perp h3,
  suffices : xperp p (l p q) (l a p),
    exact (this.2.2.2.2 (six17b p q) (six17a a p)).symm,
  exact eight15 hp.2 (six17a p q) (six17b a p),
suffices : xperp p (l p q) (l c p),
  exact (this.2.2.2.2 (six17b p q) (six17a c p)).symm,
exact eight15 hc.1 (six17a p q) (six17b c p)
end

def P : set point := planeof (P1 : point) P2 P3

theorem planeP : plane (P : set point) := ⟨P1, P2, P3, six24, rfl⟩

theorem in_P {a : point} : a ∈ (P : set point) :=
coplanar a (six14 (six26 six24).1) six24

theorem unique_plane {Q : set point} : plane Q → Q = P :=
begin
rintros ⟨x, y, z, h, h1⟩,
subst h1,
exact (nine26 h planeP in_P in_P in_P).symm
end

def dpar (A B : set point) : Prop := line A ∧ line B ∧ ¬∃ x, x ∈ A ∧ x ∈ B

def par (A B : set point) : Prop := dpar A B ∨ line A ∧ A = B

theorem line_of_par {A B : set point} : par A B → line A ∧ line B :=
λ h, h.elim (λ h, ⟨h.1, h.2.1⟩) (λ h, ⟨h.1, h.2 ▸ h.1⟩)

theorem twelve1 {A B : set point} : dpar A B → A ≠ B :=
begin
intros h h1,
rcases h.1 with ⟨x, y, h2, h3⟩,
subst_vars,
exact h.2.2 ⟨x, six17a x y, six17a x y⟩
end

theorem twelve2 {A B : set point} {a : point} : dpar A B → a ∈ A → a ∉ B :=
λ h h1 h2, h.2.2 ⟨a, h1, h2⟩

theorem twelve3 {a b c : point} : par (l a b) (l a c) → col a b c :=
begin
intro h,
cases h,
  exact (h.2.2 ⟨a, six17a a b, six17a a c⟩).elim,
change c ∈ l a b,
simp [h.2]
end

theorem par.refl {A : set point} : line A → par A A :=
λ h, or.inr ⟨h, rfl⟩

theorem dpar.symm {A B : set point} : dpar A B → dpar B A :=
λ h, ⟨h.2.1, h.1, λ ⟨x, hx⟩, h.2.2 ⟨x, hx.symm⟩⟩

theorem par.symm {A B : set point} : par A B → par B A :=
λ h, h.elim (λ h, or.inl h.symm) (λ h, or.inr ⟨h.2 ▸ h.1, h.2.symm⟩)

theorem twelve5 {A B : set point} {x : point} : par A B → x ∈ A → x ∈ B → A = B :=
λ h h1 h2, h.elim (λ h, (h.2.2 ⟨x, h1, h2⟩).elim) (and.right)

theorem twelve6 {A B : set point} : dpar A B → ∀ {b b'}, b ∈ B → b' ∈ B → side A b b' :=
begin
intros h b b' h1 h2,
have h3 : b ∉ A,
  intro h_1,
  exact h.2.2 ⟨b, h_1, h1⟩,
cases coplanar b' h.1 h3,
  exact h_1.symm,
cases h_1,
  exact (h.2.2 ⟨b', h_1, h2⟩).elim,
cases h_1.2.2.2 with x hx,
apply (h.2.2 ⟨x, hx.1, _⟩).elim,
suffices : B = l b b',
  rw this,
  exact or.inr (or.inl hx.2.symm),
exact six18 h.2.1 (nine2 h_1) h1 h2
end

theorem twelve7 {a b c d : point} : dpar (l a b) (l c d) ↔ side (l a b) c d ∧ ¬∃ x, col a b x ∧ col c d x :=
begin
split,
  intro h,
  refine ⟨twelve6 h (six17a c d) (six17b c d), _⟩,
  rintros ⟨x, hx⟩,
  exact h.2.2 ⟨x, hx.1, hx.2⟩,
rintros ⟨h, h1⟩,
have h2 := six13 (nine11 h).1,
have h3 : c ≠ d,
  intro h_1,
  subst d,
  exact h1 ⟨b, or.inl (three1 a b), or.inl (three3 c b)⟩,
refine ⟨six14 h2, six14 h3, λ h_1, _⟩,
cases h_1 with x hx,
exact h1 ⟨x, hx.1, hx.2⟩
end

theorem twelve8 (a : point) {L : set point} : line L → ∃! (A : set point), a ∈ A ∧ perp L A :=
begin
intro h,
by_cases h1 : a ∈ L,
  rcases six22 h h1 with ⟨b, hb, h2⟩,
  subst h2,
  cases eight25 hb.symm with c hc,
  refine ⟨l a c, ⟨six17a a c, _⟩, _⟩,
    suffices : xperp a (l a b) (l a c),
      exact ⟨a, this⟩,
    apply eight13.2,
    simp *,
    exact ⟨six14 hc.2.symm, b, six17b a b, c, six17b a c, hb.symm, hc.2, hc.1⟩,
  intros Y hy,
  rcases six22 (eight14e hy.2).2 hy.1 with ⟨x, hx, h2⟩,
  subst h2,
  apply six18 (six14 hx) hc.2.symm (six17a a x) _,
  apply col_of_perp hb _ hc.1.symm,
  have h2 := eight15 hy.2.symm (six17a a x) (six17a a b),
  exact h2.2.2.2.2 (six17b a x) (six17b a b),
have h2 := eight18 h h1,
cases exists_of_exists_unique h2 with x hx,
refine ⟨l a x, ⟨(six17a a x), hx.2⟩, _⟩,
intros Y hy,
apply six18 (eight14e hy.2).2 _ hy.1 _,
  intro h_1,
  subst h_1,
  exact h1 hx.1,
cases hy.2 with z hz,
suffices : z = x,
  subst z,
  exact hz.2.2.2.1,
apply unique_of_exists_unique h2 ⟨hz.2.2.1, _⟩ hx,
suffices : Y = l a z,
  subst Y,
  exact hy.2,
apply six18 (eight14e hy.2).2 _ hy.1 hz.2.2.2.1,
intro h_1,
subst h_1,
exact h1 hz.2.2.1
end

theorem twelve9 {A B C : set point} : line A → line B → line C → perp A C → perp B C → par A B :=
begin
intros h h1 h2 h3 h4,
by_cases h_1 : A = B,
  exact or.inr ⟨h, h_1⟩,
refine or.inl ⟨h, h1, λ h_2, _⟩,
cases h_2 with x hx,
apply h_1,
exact unique_of_exists_unique (twelve8 x h2) ⟨hx.1, h3.symm⟩ ⟨hx.2, h4.symm⟩
end

theorem twelve10 {A : set point} {a : point} : line A → ∃ B, par A B ∧ a ∈ B :=
begin
intro h,
by_cases h1 : a ∈ A,
  exact ⟨A, or.inr ⟨h, rfl⟩, h1⟩,
cases exists_of_exists_unique (twelve8 a h) with C hc,
cases exists_of_exists_unique (twelve8 a (eight14e hc.2).2) with B hb,
refine ⟨B, _, hb.1⟩,
exact twelve9 h (eight14e hb.2).2 (eight14e hc.2).2 hc.2 hb.2.symm
end

theorem twelve11 {A B C : set point} {a : point} : line A → a ∉ A → par A B → a ∈ B → par A C → a ∈ C → B = C :=
begin
intros h h1 h2 h3 h4 h5,
replace h2 : dpar A B,
  apply h2.elim (id),
  intro h_2,
  exact (h1 (h_2.2.symm ▸ h3)).elim,
replace h4 : dpar A C,
  apply h4.elim (id),
  intro h_2,
  exact (h1 (h_2.2.symm ▸ h5)).elim,
by_contradiction h_1,
rcases h with ⟨s, t, h, h6⟩,
subst h6,
suffices : ∃ c', c' ∈ C ∧ Bl t B c',
  rcases this with ⟨c', hc1, hc2⟩,
  cases hc2.2.2.2 with b hb,
  cases three14 c' a with c hc,
  cases pasch hc.1.symm hb.2 with d hd,
  have h6 : a ≠ b,
    intro h_2,
    subst b,
    suffices : c' ≠ a,
      apply twelve2 h4 (six17b s t),
      rw (six18 h4.2.1 this hc1 h5),
      exact or.inl hb.2.symm,
    intro h_2,
    subst h_2,
    exact hc2.2.2.1 h3,
  have h7 : c ∈ C,
    rw (six18 h4.2.1 _ hc1 h5),
    exact or.inl hc.1,
    intro h_2,
    subst h_2,
    exact hc2.2.2.1 h3,
  suffices : a ≠ d,
    rcases euclids hd.1 hd.2 this with ⟨⟨x, y⟩, hx, hy, ht⟩,
    suffices : side (l s t) a t,
      exact (nine11 this).2.2 (six17b s t),
    apply nine17a (twelve6 h2 h3 _) (twelve6 h4 h5 _) ht,
      rw six18 h2.2.1 h6 h3 hb.1,
      exact or.inl hx,
    rw six18 h4.2.1 hc.2 h5 h7,
    exact or.inl hy,
  intro h_2,
  subst h_2,
  apply h_1,
  rw [six18 h2.2.1 h6 h3 hb.1, six18 h4.2.1 hc.2 h5 h7],
  exact six16 h6 hc.2 (or.inr (or.inr hd.2.symm)),
cases six22 h4.2.1 h5 with x hx,
rw hx.2,
cases coplanar x h2.2.1 (twelve2 h2 (six17b s t)),
  refine ⟨S a x, (seven24 (six14 hx.1) (six17a a x)).1 (six17b a x), _⟩,
  exact (nine8 (nine1 h2.2.1 h3 (nine11 h_2).2.1)).2 h_2,
cases h_2,
  apply (h_1 _).elim,
  apply six21 hx.1 h2.2.1 h4.2.1 h3 h5 h_2,
  rw hx.2,
  simp,
exact ⟨x, six17b a x, h_2⟩
end

theorem twelve13 {A : set point} (a : point) : line A → ∃! B, par A B ∧ a ∈ B :=
begin
intro h,
apply exists_unique_of_exists_of_unique,
  exact twelve10 h,
intros X Y hx hy,
by_cases h_1 : a ∈ A,
  exact (twelve5 hx.1 h_1 hx.2).symm.trans (twelve5 hy.1 h_1 hy.2),
exact twelve11 h h_1 hx.1 hx.2 hy.1 hy.2
end

theorem par.trans {A B C : set point} : par A B → par B C → par A C :=
begin
intros h h1,
cases h,
  cases h1,
    rw [par, or_iff_not_and_not],
    simp [h.1],
    intro h2,
    replace h2 : ∃ x, x ∈ A ∧ x ∈ C,
      by_contradiction h_1,
      exact h2 ⟨h.1, h1.2.1, h_1⟩,
    cases h2 with x hx,
    exact twelve11 h.2.1 (twelve2 h hx.1) (or.inl h.symm) hx.1 (or.inl h1) hx.2,
  rw h1.2.symm,
  exact or.inl h,
rwa h.2
end

theorem twelve17 {a b c d p : point} : M a p c → M b p d → a ≠ b → par (l a b) (l c d) :=
begin
intros h h1 h2,
replace h := seven6 h,
replace h1 := seven6 h1,
rw [h, h1],
by_cases h3 : col a b p,
  refine or.inr ⟨six14 h2, six18 (six14 h2) (two7 (seven13 p a b) h2) _ _⟩;
  apply (seven24 (six14 h2) h3).1;
  simp,
refine or.inl ⟨six14 h2, six14 (two7 (seven13 p a b) h2), _⟩,
intro h_1,
rcases h_1 with ⟨x, hx1, hx2⟩,
have h4 : x ≠ p,
  intro h_1,
  subst p,
  exact h3 hx1,
suffices : l a b = l (S p a) (S p b),
  apply h3,
  apply (six27 (six14 h2) (six17a a b) _ (seven5 p a).1),
  simpa [this],
apply six21 (seven12b h4.symm) (six14 h2) (six14 (two7 (seven13 p a b) h2)) hx1 hx2,
  rw [←seven7 p a, ←seven7 p b],
  exact (S_of_col p).1 hx2,
exact (S_of_col p).1 hx1
end

theorem par_of_S {a b : point} (p : point) : a ≠ b → par (l a b) (l (S p a) (S p b)) :=
twelve17 (seven5 p a) (seven5 p b)

theorem twelve18 {a b c d p : point} : eqd a b c d → eqd b c d a → ¬col a b c → b ≠ d → col a p c → 
col b p d → par (l a b) (l c d) ∧ par (l b c) (l d a) ∧ Bl b (l a c) d ∧ Bl a (l b d) c :=
begin
intros h h1 h2 h3 h4 h5,
have h6 := seven21 h2 h3 h h1 h4 h5,
refine ⟨twelve17 h6.1 h6.2 (six26 h2).1, twelve17 h6.2 h6.1.symm (six26 h2).2.1, _⟩,
split,
  rw seven6 h6.2,
  exact nine1 (six14 (six26 h2).2.2) (four11 h4).1 (four10 h2).1,
rw seven6 h6.1,
apply nine1 (six14 h3) (four11 h5).1,
intro h_1,
suffices : c ∈ l b d,
  exact h2 (six23.2 ⟨l b d, six14 h3, h_1, six17a b d, this⟩),
rw seven6 h6.1,
exact (seven24 (six14 h3) (four11 h5).1).1 h_1
end

theorem twelve19 {a b c d : point} : ¬col a b c → par (l a b) (l c d) → par (l b c) (l d a) → 
eqd a b c d ∧ eqd b c d a ∧ Bl b (l a c) d ∧ Bl a (l b d) c :=
begin
intros h h1 h2,
generalize hp : mid a c = p,
replace hp : c = S p a,
  rw ←hp,
  exact (mid_to_Sa a c).symm,
subst c,
have h3 : eqd b (S p a) (S p b) a,
  have h4 := seven13 p b (S p a),
  simpa using h4,
have h4 := twelve18 (seven13 p a b) h3 h _ (or.inl (seven5 p a).1) (or.inl (seven5 p b).1),
  suffices : d = S p b,
    rw this,
    exact ⟨seven13 p a b, h3, h4.2.2.1, h4.2.2.2⟩,
  have h5 := twelve3 (h1.symm.trans h4.1),
  have h6 := (h2.symm.trans h4.2.1),
  rw [six17, six17 (S p b) a] at h6,
  replace h6 := twelve3 h6,
  by_contradiction h_1,
  apply h,
  rw S_of_col p,
  simp,
  exact (four11 (five4 (ne.symm h_1) (four11 h5).2.2.2.2 (four11 h6).2.2.2.2)).2.1,
apply seven12b,
intro h_1,
subst p,
exact h (or.inl (seven5 b a).1)
end

theorem twelve20 {a b c d : point} : par (l a b) (l c d) → eqd a b c d → Bl b (l a c) d → 
par (l b c) (l d a) ∧ eqd b c d a ∧ Bl a (l b d) c :=
begin
intros h h1 h2,
generalize hp : mid b d = p,
replace hp : d = S p b,
  rw ←hp,
  exact (mid_to_Sa b d).symm,
subst d,
have h3 : p ∉ l a b,
  intro h_1,
  suffices : a ∈ l c (S p b),
    exact h2.2.2.1 (four11 this).2.2.2.1,
  suffices : l a b = l c (S p b),
    simpa [this.symm],
  exact twelve5 h ((seven24 (line_of_par h).1 h_1).1 (six17b a b)) (six17b c (S p b)),
have h4 : par (l b (S p a)) (l (S p b) a),
  suffices : par(l b (S p a)) (l (S p b) (S p (S p a))),
    simpa [this],
  apply par_of_S p,
  intro h_1,
  subst b,
  exact (four10 h3).1 (or.inl (seven5 p a).1),
have h5 := twelve19 (λ h_1, h3 (six27 (six14 (six26 h2.2.1).2.2) (six17a a b) h_1 (seven5 p a).1)) (par_of_S p (six26 h2.2.1).2.2) h4,
suffices : c = S p a,
  subst c,
  exact ⟨h4, h5.2.1, h5.2.2.2⟩,
have h6 := h.symm.trans (par_of_S p (six26 h2.2.1).2.2),
rw [six17, six17 (S p a)] at h6,
apply six11a (six4.2 ⟨(four11 (twelve3 h6)).2.1, _⟩) (h1.symm.flip.trans (seven13 p a b).flip),
intro h_1,
have h7 : p ∉ l a c,
  intro h_2,
  apply h2.2.1,
  apply six27 h2.1 ((seven24 h2.1 h_2).1 (six17b a c)) (six17a a c),
  rw [←seven7 p a, ←seven7 p b],
  exact (seven15 p).1 h_1,
apply nine9 h2,
suffices : side (l a c) (S p a) (S p c),
  apply side.trans _ (this.symm.trans _),
    suffices : sided a b (S p c),
      exact nine12 h2.1 (six17a a c) this h2.2.1,
    apply six7 _ (six26 h2.2.1).2.2.symm,
    rw [←seven7 p a, ←seven7 p b],
    exact (seven15 p).1 h_1.symm,
  suffices : sided c (S p b) (S p a),
    exact (nine12 h2.1 (six17b a c) this h2.2.2.1).symm,
  exact six7 h_1 (six13 (line_of_par h).2).symm,
suffices : side (l a c) p (S p a),
  apply this.symm.trans,
  apply nine12 h2.1 (six17b a c) (six7 (seven5 p c).1 _) h7,
  intro h_1,
  subst p,
  exact h7 (six17b a c),
apply nine12 h2.1 (six17a a c) (six7 (seven5 p a).1 _) h7,
intro h_1,
subst p,
exact h7 (six17a a c)
end

theorem twelve21 {a b c d : point} : Bl b (l a c) d → (par (l a b) (l c d) ↔ eqa b a c d c a) :=
begin
intro h,
cases exists_of_exists_unique (six11 (six26 h.2.2.1).2.1.symm
  (six26 h.2.1).2.2) with d' hd,
replace h : Bl b (l a c) d',
    apply ((nine8 h.symm).2 _).symm,
    exact nine12 h.1 (six17b a c) hd.1.symm h.2.2.1,
split,
  intro h1,
  rw (six16a hd.1.symm) at h1,
  suffices : eqa b a c d' c a,
    exact eleven10 this (six5 this.1) (six5 this.2.1) hd.1.symm (six5 this.2.2.2.1),
  apply eleven11 (six13 (line_of_par h1).1).symm (six13 h.1).symm,
  exact ⟨hd.2.symm.flip, eqd_refl a c, (twelve20 h1 hd.2.symm h).2.1⟩,
intro h1,
replace h1 := eleven10 h1 (six5 h1.1) (six5 h1.2.1) hd.1 (six5 h1.2.2.2.1),
rw (six16a hd.1.symm),
apply (twelve18 hd.2.symm (SAS h1 hd.2.symm.flip (eqd_refl c a)).1 (four10 h.2.1).1 (nine2 h) (or.inl (ten1 a c).1) _).1,
suffices : d' = S (mid a c) b,
  rw this,
  exact or.inl (seven5 (mid a c) b).1,
apply six11a _,
  apply hd.2.trans,
  suffices : eqd a b (S (mid a c) a) (S (mid a c) b),
    simpa [(mid_to_Sa a c)] using this,
  exact (seven13 (mid a c) a b),
apply eleven15b h.2.2.1 h.2.2.1 (eqa.refl h1.2.2.2.1 h1.2.2.1) (side.refla (four10 h.2.2.1).2.1),
  apply h1.symm.flip.trans,
  simpa [mid_to_Sa a c, mid_to_Sb a c] using (eleven12 (mid a c) h1.2.1 h1.1),
rw six17,
exact ((nine8 h.symm).1 ((nine1 h.1 (or.inr (or.inl (ten1 a c).1.symm)) h.2.1).symm)).symm
end

theorem twelve22 {a b c d p : point} : sided p a c → side (l p a) b d → (par (l a b) (l c d) ↔ eqa b a p d c p) :=
begin
intros h h1,
generalize hp : mid p a = q,
replace hp : p = S q a,
  rw ←hp,
  exact (mid_to_Sb p a).symm,
subst p,
have h2 := eleven12 q (six26 (nine11 h1).2.1).2.1.symm h.1.symm,
rw seven7 at h2,
replace h2 := eleven10 h2 (six5 h2.1) (six5 h2.2.1) (six5 h2.2.2.1) h.symm,
have h3 := par_of_S q (six26 (nine11 h1).2.1).2.1,
have h4 : Bl (S q b) (l (S q a) c) d,
  exact (six16a h) ▸ ((nine8 (nine1 (nine11 h1).1 (or.inr (or.inl (seven5 q a).1)) (nine11 h1).2.1)).2 h1).symm,
exact ⟨λ h5, h2.trans ((twelve21 h4).1 (h3.symm.trans h5)), λ h5, h3.trans ((twelve21 h4).2 (h2.symm.trans h5))⟩
end

theorem twelve23 {a b c : point} : ¬col a b c → ∃ b' c', Bl b (l a c) b' ∧ Bl c (l a b) c' ∧ 
B b' a c' ∧ eqa a b c b a c' ∧ eqa a c b c a b' :=
begin
intro h,
have h1 := nine1 (six14 (six26 h).2.2) (or.inr (or.inl (ten1 a c).1.symm)) (four10 h).1,
have h2 := nine1 (six14 (six26 h).1) (or.inr (or.inl (ten1 a b).1.symm)) h,
have h3 := eleven12 (mid a b) (six26 h).1 (six26 h).2.1.symm,
have h4 := eleven12 (mid a c) (six26 h).2.2 (six26 h).2.1,
simp at h3 h4,
refine ⟨S (mid a c) b, S (mid a b) c, h1, h2, _, h3, h4⟩,
have h5 : col a (S (mid a c) b) (S (mid a b) c),
  apply twelve3,
  rw six17 at h1 h2,
  suffices : par (l b c) (l a (S (mid a c) b)),
    exact this.symm.trans ((twelve21 h2).2 h3.flip),
  exact six17 c b ▸ ((twelve21 h1).2 h4.flip),
exact ((nine18 h2.1 (six17a a b) (four11 h5).2.2.1).1 ((nine8 h2).2 (nine15 (λ h_1, h (mid_to_Sa a c
 ▸ (seven24 h2.1 h_1).1 (six17a a b))) (ten1 a c).1 (seven5 (mid a c) b).1))).1
end

end Euclidean_plane