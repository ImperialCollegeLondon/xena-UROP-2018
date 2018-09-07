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
cases ten15 h hp.2.2.1 h2 with c hc,
suffices : col p a c,
  by_cases h_1 : B c p a,
    apply (or.inr (or.inr ((nine8 _).2 hc.2).symm)),
    exact ⟨h, (nine11 hc.2).2.1, h1, p, hp.2.2.1, h_1⟩,
  apply or.inl (hc.2.symm.trans _),
  exact nine12 h hp.2.2.1 (six4.2 ⟨(four11 this).2.2.2.1, h_1⟩) (nine11 hc.2).2.1,
rcases six22 h hp.2.2.1 with ⟨q, h3, h4⟩,
subst h4,
apply col_of_perp h3,
  suffices : xperp p (l p q) (l a p),
    exact (this.2.2.2.2 (six17b p q) (six17a a p)).symm,
  exact eight15 ⟨p, hp⟩ (six17a p q) (six17b a p),
suffices : xperp p (l p q) (l c p),
  exact (this.2.2.2.2 (six17b p q) (six17a c p)).symm,
exact eight15 hc.1 (six17a p q) (six17b c p)
end

def Pl : set point := planeof (P1 : point) P2 P3

theorem planePl : plane (Pl : set point) := ⟨P1, P2, P3, six24, rfl⟩

theorem in_Pl {a : point} : a ∈ (Pl : set point) :=
coplanar a (six14 (six26 six24).1) six24

theorem unique_plane {Q : set point} : plane Q → Q = Pl :=
begin
rintros ⟨x, y, z, h, h1⟩,
subst h1,
exact (nine26 h planePl in_Pl in_Pl in_Pl).symm
end

theorem unique_perp (a : point) {L : set point} : line L → ∃! A : set point, a ∈ A ∧ perp L A :=
begin
intro h,
by_cases h_1 : a ∈ L,
  rcases six22 h h_1 with ⟨b, h1, hb⟩,
  subst hb,
  rcases eight21 h1 a with ⟨p, t, hp, ht⟩,
  clear ht,
  replace hp := eight15 hp (six17a a b) (six17b p a),
  refine exists_unique.intro (l p a) ⟨six17b p a, a, hp⟩ _,
  intros Y hy,
  apply six18 (eight14e hy.2).2 (six13 hp.2.1) _ hy.1,
  rcases six22 (eight14e hy.2).2 hy.1 with ⟨z, hz, h5⟩,
  subst h5,
  replace hy := (eight15 hy.2 (six17a a b) (six17a a z)).symm.2.2.2.2,
  exact col_of_perp h1 (hy (six17b a z) (six17b a b)) (hp.symm.2.2.2.2 (six17a p a) (six17b a b)),
cases eight17 h h_1 with x hx,
dsimp at hx,
refine ⟨l a x, ⟨(six17a a x), x, hx.1⟩, _⟩,
rintros Y ⟨h1, y, h2⟩,
suffices : Y = l a y,
  subst this,
  rw (hx.2 y h2),
apply six18 h2.2.1 _ h1 h2.2.2.2.1,
intro h_2,
subst y,
exact h_1 h2.2.2.1
end

theorem unique_xperp {a : point} {L : set point} : line L → a ∈ L → ∃! A : set point, xperp a L A :=
begin
intros h h1,
rcases (unique_perp a h) with ⟨A, h2, h3⟩,
exact ⟨A, eight15 h2.2 h1 h2.1, λ Y hy, h3 Y ⟨hy.2.2.2.1, a, hy⟩⟩
end

theorem eleven15d {a b c d : point} (h : eqa a b c a b d) : sided b c d ∨ sided b c (Sl (six14 h.1) d) :=
begin
generalize : six14 h.1 = h1,
by_cases h_1 : col a b c,
  left,
  cases six1 h_1,
    exact ⟨h.2.1, h.2.2.2.1, five2 h.1 h_2 (eleven21b h_2 h)⟩,
  exact h_2.symm.trans ((eleven21a h_2).1 h),
cases coplanar d h1 h_1,
  exact or.inl (eleven15c h h_2.symm),
cases h_2,
  exact (h_1 (eleven21d h_2 h.symm)).elim,
right,
have h2 : side (l a b) c (Sl h1 d),
  exact ⟨d, h_2, (ten14 h1 h_2.2.2.1).symm⟩,
apply eleven15c (h.trans _) h2,
simpa [ten3b h1 (six17a a b), ten3b h1 (six17b a b)] using eleven12a h1 h.1 h.2.2.2.1
end

-- Parallel lines

def dpar (A B : set point) : Prop := line A ∧ line B ∧ ¬∃ x, x ∈ A ∧ x ∈ B

def par (A B : set point) : Prop := dpar A B ∨ line A ∧ A = B

theorem dpar_of_par_neq {A B : set point} : par A B → A ≠ B → dpar A B :=
λ h h1, h.elim id (λ h_1, absurd h_1.2 h1)

theorem line_of_par {A B : set point} : par A B → line A ∧ line B :=
λ h, h.elim (λ h, ⟨h.1, h.2.1⟩) (λ h, ⟨h.1, h.2 ▸ h.1⟩)

theorem is_of_not_par {A B : set point} : line A → line B → ¬par A B → ∃ x, is x A B :=
begin
intros h h1 h2,
rw [par, not_or_distrib] at h2,
have h3 : ∃ x, x ∈ A ∧ x ∈ B,
  by_contradiction h_1,
  exact h2.1 ⟨h, h1, h_1⟩,
cases h3 with x hx,
refine ⟨x, h, h1, _, hx.1, hx.2⟩,
intro h_1,
subst B,
exact h2.2 ⟨h1, rfl⟩
end

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
have h2 := eight17 h h1,
cases exists_of_exists_unique h2 with x hx,
refine ⟨l a x, ⟨(six17a a x), x, hx⟩, _⟩,
intros Y hy,
apply six18 (eight14e hy.2).2 _ hy.1 _,
  intro h_1,
  subst h_1,
  exact h1 hx.2.2.1,
cases hy.2 with z hz,
suffices : z = x,
  subst z,
  exact hz.2.2.2.1,
apply unique_of_exists_unique h2 _ hx,
suffices : Y = l a z,
  subst Y,
  exact hz,
apply six18 (eight14e hy.2).2 _ hy.1 hz.2.2.2.1,
intro h_1,
subst h_1,
exact h1 hz.2.2.1
end

theorem twelve9 {A B C : set point} : perp A C → perp B C → par A B :=
begin
intros h h1,
by_cases h_1 : A = B,
  exact or.inr ⟨(eight14e h).1, h_1⟩,
refine or.inl ⟨(eight14e h).1, (eight14e h1).1, λ h_2, _⟩,
cases h_2 with x hx,
apply h_1,
exact unique_of_exists_unique (twelve8 x (eight14e h1).2) ⟨hx.1, h.symm⟩ ⟨hx.2, h1.symm⟩
end

theorem twelve10 {A : set point} {a : point} : line A → ∃ B, par A B ∧ a ∈ B :=
begin
intro h,
by_cases h1 : a ∈ A,
  exact ⟨A, or.inr ⟨h, rfl⟩, h1⟩,
cases exists_of_exists_unique (twelve8 a h) with C hc,
cases exists_of_exists_unique (twelve8 a (eight14e hc.2).2) with B hb,
exact ⟨B, twelve9 hc.2 hb.2.symm, hb.1⟩
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
apply eleven15b h.2.2.1 h.2.2.1 (eqa.refl h1.2.2.2.1 h1.2.2.1) (side.refla h.2.2.1),
  apply h1.symm.flip.trans,
  simpa [mid_to_Sa a c, mid_to_Sb a c] using (eleven12 (mid a c) h1.2.1 h1.1),
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
  exact (six26 h).1 (unique_of_exists_unique (seven4 p c) h2 h1),
cases exists_of_exists_unique (eight17 (six14 (six26 h4).1) h4) with c' hc,
cases exists_of_exists_unique (eight22 (S q c') (S p c')) with x hx,
cases exists_of_exists_unique (unique_perp x hc.1) with A' hA,
suffices : A = A',
  exact this.symm ▸ hA.2.symm,
apply unique_of_exists_unique (unique_xperp g1.2.1 g1.2.2.2.1) g1.symm,
have h5 := (eight14e hA.2).2,
suffices : Sl h5 a = b,
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
have h7 : Sl h5 (S q c') = S p c',
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
        suffices : R (Sl h5 (S p c')) (Sl h5 (S q c')) (Sl h5 a),
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
      exact (nine11 this).2.1 (h_1.symm ▸ six17a a (Sl h5 a)),
    exact eqa.refl (six26 (nine11 this).2.2).1 (six26 (nine11 this).2.2).2.1.symm,
  rw [h6, seven6 h2, seven6 h1],
  exact ⟨c, (nine16 (six14 (six26 h4).1) h4 (six17b p q)).symm, (nine16 (six14 (six26 h4).1) h4 (six17a p q)).symm⟩,
apply (ten10 h5 (S p c') (Sl h5 a)).trans,
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
replace h5 := eleven49 h5,
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
have ha := six14 he.2.2.2.2.2.1.symm,
rw six17 (S d b) (S c b),
suffices : Sl ha (S c b) = S d b,
  rw ←this,
  refine eight15 (ten3a ha _).2 (ten3a ha _).1 (or.inr (or.inl (ten1 (S c b) (Sl ha (S c b))).1.symm));
  intro h_1;
  exact (seven18a b (nine2 h)) (this ▸ (ten3b ha h_1).symm),
suffices : eqa (S c b) a e' (S d b) a e',
  cases eleven15d this.flip,
    exact ((seven18a b (nine2 h)) (six11a h_1 h8)).elim,
  rw Sl.symm at h_1,
  change sided a (S c b) (Sl ha (S d b)) at h_1,
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
  replace h6 := (nine11 h6).1,
  suffices : S d b = Sl h6 b,
    rw this,
    simpa [ten3b h6 (six17a a d), ten3b h6 (six17b a d)] using eleven12a h6 h7.2.1 h7.1,
  apply unique_of_Sl h6 (four10 h.2.2.1).1 _ (perp_of_R h7.2.1.symm (six26 h.2.2.1).2.1 h2.symm),
  simp [mid_of_S d b, six17b a d],
apply (he.2.2.symm.trans _).symm.flip,
replace h4 := (nine11 h4).1,
suffices : S c b = Sl h4 b,
  rw this,
  simpa [ten3b h4 (six17a a c), ten3b h4 (six17b a c)] using eleven12a h4 he.2.2.1 h7.1,
apply unique_of_Sl h4 (four10 h.2.1).1 _ (perp_of_R he.2.2.1.symm (six26 h.2.1).2.1 h1.symm),
simp [mid_of_S c b, six17b a c]
end

end Euclidean_plane