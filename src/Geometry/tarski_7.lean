import geometry.tarski_6
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance, priority 0] prop_decidable 

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

theorem eleven15d {a b c d : point} (h : eqa a b c a b d) (h1 : line (l a b)) : sided b c d ∨ sided b c (Sl (l a b) d) :=
begin
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
have h2 : side (l a b) c (Sl (l a b) d),
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

theorem thirteen8 {o p q u v : point} : col o p q → col o u v → o ≠ u → o ≠ v → R o u p → R o v q → 
(sided o p q ↔ sided o u v) :=
begin
intros h h1 h2 h3 h4 h5,
by_cases h_1 : col o u p,
  cases eight9 h4 h_1,
    exact (h2 h_2).elim,
  subst p,
  cases eight9 h5 (five4 h2 h1 h),
    exact (h3 h_2).elim,
  rw h_2,
have h6 : q ≠ v,
  intro h_1,
  subst q,
  exact h_1 (six23.2 ⟨l o v, six14 h3, six17a o v, (four11 h1).1, (four11 h).1⟩),
have h7 : xperp u (l o u) (l p u),
  exact eight13.2 ⟨six14 h2, six14 (six26 h_1).2.1.symm, six17b o u, six17b p u, o, p, six17a o u, six17a p u, h2, (six26 h_1).2.1.symm, h4⟩,
have h8 : xperp v (l o u) (l q v),
  exact eight13.2 ⟨six14 h2, six14 h6, h1, six17b q v, o, q, six17a o u, six17a q v, h3, h6, h5⟩,
cases exists_of_exists_unique (unique_perp o (six14 h2)) with L hl,
replace h7 := twelve9 hl.2.symm ⟨u, h7.symm⟩,
replace h8 := twelve9 hl.2.symm ⟨v, h8.symm⟩,
cases h7,
  cases h8,
    replace h7 := twelve6 h7 (six17a p u) (six17b p u),
    replace h8 := twelve6 h8 (six17a q v) (six17b q v),
    split,
      intro h9,
      apply (nine19 (nine11 h7).1 hl.1 (four11 h1).2.2.1 (h7.symm.trans (side.trans _ h8))).1,
      exact nine12 (nine11 h7).1 hl.1 h9 (nine11 h7).2.1,
    intro h9,
    apply (nine19 (nine11 h7).1 hl.1 (four11 h).2.2.1 (h7.trans (side.trans _ h8.symm))).1,
    exact nine12 (nine11 h7).1 hl.1 h9 (nine11 h7).2.2,
  rw h8.2 at *,
  exact ((eight9 h5.symm hl.1).elim h6 h3).elim,
rw h7.2 at *,
exact (h_1 (four11 hl.1).2.2.2.2).elim
end

lemma twelve24a {a b c d e f x y : point} : eqa a b c d e f → xperp x (l b c) (l a x) → xperp y (l e f) (l d y) → sided b c x → sided e f y :=
begin
intros h h1 h2 h3,
replace h := eleven10 h (six5 h.1) h3.symm (six5 h.2.2.1) (six5 h.2.2.2.1),
rw (six16a h3) at h1,
clear h3,
rcases eleven5.1 h with ⟨p, q, h3⟩,
have h4 : R e q p,
  exact eleven17 (h1.2.2.2.2 (six17a b x) (six17a a x)) (eleven11 h.2.1.symm (six13 h1.2.1) (four4 h3.2.2).2.2.1),
have h5 : R e y d,
  exact h2.2.2.2.2 (six17a e f) (six17a d y),
apply h3.2.1.symm.trans ((thirteen8 (four11 (six4.1 h3.1).1).2.1 _ h3.2.1.1.symm _ h4 h5).1 h3.1),
  show y ∈ l e q,
  rw six16a h3.2.1,
  exact h2.2.2.1,
intro h_1,
subst y,
have h6 : R d e f,
  exact h2.symm.2.2.2.2 (six17a d e) (six17b e f),
apply h.2.1,
exact eight7 (h1.symm.2.2.2.2 (six17a a x) (six17a b x)) (eleven17 h6 h.symm)
end

theorem twelve24 {a b c d e f x y : point} : eqa a b c d e f → xperp x (l b c) (l a x) → xperp y (l e f) (l d y) → (sided b c x ↔ sided e f y) :=
λ h h1 h2, ⟨twelve24a h h1 h2, twelve24a h.symm h2 h1⟩

-- distance + angle interface

instance eqd_setoid : setoid (point × point) :=
{ r := λ a b, eqd a.1 a.2 b.1 b.2,
  iseqv := ⟨ λ ⟨a,b⟩, eqd.refl a b, λ ⟨a,b⟩ ⟨c,d⟩, eqd.symm, λ ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩, eqd.trans⟩
}

definition dist (point : Type) [Euclidean_plane point] := 
quotient (@Euclidean_plane.eqd_setoid point _)

instance dist_order : linear_order (dist point) :=
{ le := λ a b, quotient.lift_on₂ a b (λ x y, distle x.1 x.2 y.1 y.2) (λ a b c d h h1,
    begin rw ←iff_iff_eq, split; intro h2, exact five6 h2 h h1, exact five6 h2 h.symm h1.symm end),
  le_refl := λ a, quotient.induction_on a $ λ x, distle.refl x.1 x.2,
  le_trans := λ a b c, quotient.induction_on₃ a b c $ λ x y z, distle.trans,
  le_antisymm := λ a b, quotient.induction_on₂ a b $
    λ x y h h1, quotient.sound (five9 h h1),
  le_total := λ a b, quotient.induction_on₂ a b $
    λ x y, five10 x.1 x.2 y.1 y.2 }

instance zero_dist : has_zero (dist point) := ⟨⟦(P1, P1)⟧⟩

@[simp] theorem zero_dist_def : ⟦(P1, P1)⟧ = (0 : dist point) := rfl

@[simp] theorem zero_class (a : point) : ⟦(a, a)⟧ = (0 : dist point) :=
quotient.sound (two8 a P1)

theorem eq_of_zero_dist {a b  : point} : ⟦(a, b)⟧ = (0 : dist point) → a = b :=
λ h, id_eqd (quotient.exact (h.trans zero_dist_def.symm))

theorem non_zero_dist_of_neq {a b : point} : a ≠ b → ⟦(a, b)⟧ ≠ (0 : dist point) :=
λ h h1, h (id_eqd (quotient.exact h1))

def seg_cons_dist {a b : point} (hab : a ≠ b) (D : dist point) : {x // B a b x ∧ quotient.mk (b, x) = D} :=
⟨quotient.lift_on D (λ x : point × point, (seg_cons b x.1 x.2 a).1) 
(begin
rintros ⟨x, y⟩ ⟨p, q⟩ h,
dsimp,
generalize h1 : seg_cons b x y a = z,
generalize h2 : seg_cons b p q a = r,
exact two12 hab z.2.1 z.2.2 r.2.1 (r.2.2.trans h.symm)
end), begin apply quotient.induction_on D,
rintros ⟨x, y⟩,
exact ⟨(seg_cons b x y a).2.1, quotient.sound (seg_cons b x y a).2.2⟩ end⟩

def set_angle (point : Type) := {x : point × point × point // x.1 ≠ x.2.1 ∧ x.2.2 ≠ x.2.1}

def eqa_set_angle (x y : set_angle point) : Prop := eqa x.1.1 x.1.2.1 x.1.2.2 y.1.1 y.1.2.1 y.1.2.2

instance eqa_setoid : setoid (set_angle point) :=
{ r := eqa_set_angle, iseqv := ⟨ λ x, eqa.refl x.2.1 x.2.2, λ x y, eqa.symm, λ x y z, eqa.trans⟩
}

definition angle (point : Type) [Euclidean_plane point] := 
quotient (@Euclidean_plane.eqa_setoid point _)

instance angle_order : linear_order (angle point) :=
{ le := λ α β, quotient.lift_on₂ α β (λ x y, ang_le x.1.1 x.1.2.1 x.1.2.2 y.1.1 y.1.2.1 y.1.2.2) (λ a b c d h h1, 
    begin rw ←iff_iff_eq, split; intro h2, exact eleven30 h2 h h1, exact eleven30 h2 h.symm h1.symm end),
  le_refl := λ α, quotient.induction_on α $ λ x, ang_le.refl x.2.1 x.2.2,
  le_trans := λ α β γ, quotient.induction_on₃ α β γ $ λ x y z, ang_le.trans,
  le_antisymm := λ α β, quotient.induction_on₂ α β $
    λ x y h h1, quotient.sound (eleven34 h h1),
  le_total := λ α β, quotient.induction_on₂ α β $
    λ x y, eleven35 x.2.1 x.2.2 y.2.1 y.2.2 }

instance zero_angle : has_zero (angle point) := ⟨⟦⟨⟨P1, P2, P1⟩, three13, three13⟩⟧⟩

theorem zero_angle_def : (0 : angle point) = ⟦⟨⟨P1, P2, P1⟩, three13, three13⟩⟧ := rfl 

theorem zero_iff_sided {α : angle point} {x : set_angle point} (hx : ⟦x⟧ = α) : α = (0 : angle point) ↔ sided x.1.2.1 x.1.1 x.1.2.2 :=
⟨λ h, (eleven21a (six5 three13)).1 (quotient.exact (hx.trans h).symm), λ h, hx.symm.trans (quotient.sound ((eleven21a h).2 (six5 three13)))⟩

def acute_triple (x : set_angle point) : Prop := ang_acute x.1.1 x.1.2.1 x.1.2.2

theorem acute_well_defined (α β : set_angle point) : α ≈ β → acute_triple α = acute_triple β :=
begin
intro h,
suffices : acute_triple α ↔ acute_triple β,
  rw this,
split,
  intro h1,
  exact acute_trans h1 h,
intro h1,
exact acute_trans h1 h.symm
end

def acute := quotient.lift acute_triple (@acute_well_defined point _)

def obtuse_triple (x : set_angle point) : Prop := ang_obtuse x.1.1 x.1.2.1 x.1.2.2

theorem obtuse_well_defined (α β : set_angle point) : α ≈ β → obtuse_triple α = obtuse_triple β :=
begin
intro h,
suffices : obtuse_triple α ↔ obtuse_triple β,
  rw this,
split,
  intro h1,
  exact obtuse_trans h1 h,
intro h1,
exact obtuse_trans h1 h.symm
end

def obtuse := quotient.lift obtuse_triple (@obtuse_well_defined point _)

def right_triple (x : set_angle point) : Prop := ang_right x.1.1 x.1.2.1 x.1.2.2

theorem right_well_defined (α β : set_angle point) : α ≈ β → right_triple α = right_triple β :=
begin
intro h,
suffices : right_triple α ↔ right_triple β,
  rw this,
split,
  intro h1,
  exact right_trans h1 h,
intro h1,
exact right_trans h1 h.symm
end

def right := quotient.lift right_triple (@right_well_defined point _)

theorem angle_trichotomy (α : angle point) : acute α ∨ right α ∨ obtuse α :=
begin
rcases quotient.exists_rep α with ⟨⟨⟨a, b, c⟩, h⟩, h1⟩,
rw ←h1,
unfold acute right obtuse,
dsimp,
unfold acute_triple right_triple obtuse_triple,
dsimp,
exact right_total h.1 h.2
end

noncomputable def thirteen3 {a b c : point} {C : dist point} : ¬col a b c → C ≠ 0 → {x : point × point // sided b a x.1 ∧ ⟦(b, x.1)⟧ = C ∧ xperp x.2 (l b c) (l x.1 x.2)} :=
begin
intros h h1,
cases three14 a b with d hd,
cases seg_cons_dist hd.2.symm C with p hp,
have h2 : b ≠ p,
  intro h_1,
  subst p,
  apply h1,
  rw ←zero_class b,
  exact hp.2.symm,
have h3 : sided b a p,
  exact ⟨(six26 h).1, h2.symm, five2 hd.2.symm hd.1.symm hp.1⟩,
have h4 : ¬col b c p,
  intro h_1,
  apply (four10 h).2.1,
  exact five4 h2 (four11 (six4.1 h3).1).2.2.1 (four11 h_1).1,
cases indefinite_description (λ x, xperp x (l b c) (l p x)) (exists_of_exists_unique (eight17 (six14 (six26 h).2.1) h4)) with x hx,
exact ⟨⟨p, x⟩, h3, hp.2, hx⟩
end

noncomputable def cos_triple (x : set_angle point) (C : dist point) : dist point :=
if h : C = 0 then 0 else
(if h1 : (col x.1.1 x.1.2.1 x.1.2.2) then C else (
quotient.mk ((((x.val).snd).fst), (thirteen3 h1 h).1.2)))

noncomputable def cos (α : angle point) (C : dist point) : dist point :=
quotient.lift_on α (λ x : set_angle point, cos_triple x C) (λ x y h, 
begin
dsimp,
unfold cos_triple,
by_cases h1 : C = 0,
  rw [dif_pos h1, dif_pos h1],
rw [dif_neg h1, dif_neg h1],
rcases x with ⟨⟨a, b, c⟩, h2⟩,
rcases y with ⟨⟨d, e, f⟩, h3⟩,
dsimp [- ne.def] at *,
change eqa a b c d e f at h,
by_cases h4 : col a b c,
  have h5 := eleven21d h4 h,
  rw [dif_pos h4, dif_pos h5],
have h5 : ¬col d e f,
  intro h_1,
  exact h4 (eleven21d h_1 h.symm),
rw [dif_neg h4, dif_neg h5],
apply quotient.sound,
rcases thirteen3 h4 h1 with ⟨⟨p, x⟩, h6⟩,
rcases thirteen3 h5 h1 with ⟨⟨q, y⟩, h7⟩,
dsimp at h7 h6 ⊢,
replace h := eleven10 h h6.1.symm (six5 h.2.1) h7.1.symm (six5 h.2.2.2.1),
cases six1 (four11 h6.2.2.2.2.1).2.1,
  by_cases h_2 : b = x,
    subst x,
    suffices : e = y,
      subst y,
      exact two8 b e,
    have h8 : xperp e (l e f) (l q e),
      exact eight13.2 ⟨h7.2.2.1, six14 h.2.2.1, six17a e f, six17b q e, f, q, six17b e f, 
      six17a q e, h3.2, h.2.2.1, eleven17 (h6.2.2.2.2.2.2 (six17b b c) (six17a p b)) h.flip⟩,
    have h9 : ¬col e f q,
      intro h_2,
      exact h5 (eleven21d (four11 h_2).2.2.2.1 (eleven9 h7.1 (six5 h3.2))),
    exact unique_of_exists_unique (eight17 h8.1 h9) h8 h7.2.2,
  have h_3 : e ≠ y,
    intro h_3,
    subst y,
    have h8 : xperp b (l b c) (l p b),
      exact eight13.2 ⟨h6.2.2.1, six14 h.1, six17a b c, six17b p b, c, p, six17b b c, 
      six17a p b, h2.2, h.1, eleven17 (h7.2.2.2.2.2.2 (six17b e f) (six17a q e)) h.symm.flip⟩,
    have h9 : ¬col b c p,
      intro h_2,
      exact h4 (eleven21d (four11 h_2).2.2.2.1 (eleven9 h6.1 (six5 h2.2))),
    exact h_2 (unique_of_exists_unique (eight17 h8.1 h9) h8 h6.2.2),
  replace h := eleven13 h.flip (ne.symm h_2) h_1 h_3.symm _,
  apply (AAS _ _ h.flip (quotient.exact (h6.2.1.trans h7.2.1.symm)).flip).2.1,
      intro h_4,
      apply eight14b h6.2.2 (six18 h6.2.2.1 (six13 h6.2.2.2.1) _ h6.2.2.2.2.1),
      exact six23.2 ⟨l b x, six14 h_2, six17a b x, or.inr (or.inr h_1), (four11 h_4).2.2.1⟩,
    exact eleven16 h_2 (six13 h6.2.2.2.1) h_3 (six13 h7.2.2.2.1) 
    (h6.2.2.2.2.2.2 (six17a b c) (six17a p x)) (h7.2.2.2.2.2.2 (six17a e f) (six17a q y)),
  by_contradiction h_4,
  suffices : sided e f y,
    exact (six4.1 ((twelve24 h h6.2.2 h7.2.2).2 this)).2 h_1,
  simpa [h_4] using (six1 (four11 h7.2.2.2.2.1).2.1),
have h8 : sided e f y,
  exact (twelve24 h h6.2.2 h7.2.2).1 h_1,
replace h := eleven10 h (six5 h.1) h_1.symm (six5 h.2.2.1) h8.symm,
apply (AAS _ _ h (quotient.exact (h6.2.1.trans h7.2.1.symm)).flip).2.1,
  intro h_2,
  apply eight14b h6.2.2 (six18 h6.2.2.1 (six13 h6.2.2.2.1) _ h6.2.2.2.2.1),
  rw (six16a h_1),
  exact (four11 h_2).2.2.1,
exact eleven16 h_1.2.1.symm (six13 h6.2.2.2.1) h8.2.1.symm (six13 h7.2.2.2.1) 
(h6.2.2.2.2.2.2 (six17a b c) (six17a p x)) (h7.2.2.2.2.2.2 (six17a e f) (six17a q y))
end)

theorem thirteen5a {α : angle point} {x : set_angle point} {d : point} : 
⟦x⟧ = α → ¬col x.1.1 x.1.2.1 x.1.2.2 → xperp d (l x.1.2.1 x.1.2.2) (l x.1.1 d) → ⟦(x.1.2.1, d)⟧ = cos α ⟦(x.1.1, x.1.2.1)⟧ :=
begin
intros h h1 h2,
rcases x with ⟨⟨a, b, c⟩, h3, h4⟩,
rw [←h, cos],
unfold cos_triple,
dsimp at *,
rw [dif_neg (non_zero_dist_of_neq h3), dif_neg h1, quotient.sound],
rcases thirteen3 h1 (non_zero_dist_of_neq h3) with ⟨⟨p, t⟩, ht⟩,
dsimp at *,
suffices : t = d,
  rw this,
suffices : p = a,
  subst p,
  exact unique_of_exists_unique (eight17 h2.1 (four10 h1).2.2.1) ht.2.2 h2,
exact unique_of_exists_unique (six11 h3 h3) ⟨ht.1.symm, quotient.exact ht.2.1⟩ ⟨six5 h3, eqd_refl b a⟩
end

theorem thirteen5b {a b c : point} {C : dist point} (h : a ≠ b) (h1 : c ≠ b) : R a c b → ⟦(c, b)⟧ = cos ⟦⟨(a, b, c), ⟨h, h1⟩⟩⟧ ⟦(a, b)⟧ :=
begin
intro h2,
unfold cos cos_triple,
dsimp,
rw dif_neg (non_zero_dist_of_neq h),
by_cases h_1 : col a b c,
  rw dif_pos h_1,
  suffices : c = a,
    rw this,
  exact (eight9 h2 (four11 h_1).1).elim eq.symm (λ h_2, (h1.symm h_2).elim),
rw dif_neg h_1,
rcases thirteen3 h_1 (non_zero_dist_of_neq h) with ⟨⟨p, x⟩, h3⟩,
dsimp at h3 ⊢,
suffices : x = c,
  rw this,
  exact quotient.sound (eqd_refl c b),
suffices : p = a,
  subst p,
  exact unique_of_exists_unique (eight17 h3.2.2.1 (four10 h_1).2.2.1) h3.2.2 (eight13.2 ⟨h3.2.2.1, 
  six14 (six26 h_1).2.2, six17b b c, six17b a c, b, a, six17a b c, six17a a c, h1.symm, (six26 h_1).2.2, h2.symm⟩),
exact unique_of_exists_unique (six11 h3.1.1 h3.1.1) ⟨h3.1.symm, quotient.exact h3.2.1⟩ ⟨six5 h, eqd_refl b a⟩
end

theorem cos_zero {C : dist point} : cos 0 C = C :=
begin
show cos_triple ⟨⟨P1, P2, P1⟩, three13, three13⟩ C = C,
unfold cos_triple,
by_cases h_1 : C = 0,
  rw [dif_pos h_1, h_1],
rw [dif_neg h_1, dif_pos (four11 (four12 P1 P2)).1]
end

theorem cos_times_zero (α : angle point) : cos α 0 = 0 :=
begin
cases quotient.exists_rep α with x hx,
rw ←hx,
dsimp [cos, cos_triple],
rw dif_pos rfl
end

theorem thirteen6a {C : dist point} {α : angle point} : C ≠ 0 → cos α C = 0 → right α :=
begin
unfold cos cos_triple,
intros h h1,
simp only [dif_neg h] at h1,
rcases quotient.exists_rep α with ⟨⟨⟨a, b, c⟩, h2, h3⟩, h4⟩,
rw ←h4 at h1 ⊢,
dsimp at *,
by_cases h_1 : col a b c,
  rw dif_pos h_1 at h1,
  exact (h h1).elim,
rw dif_neg h_1 at h1,
rcases thirteen3 h_1 h with ⟨⟨p, x⟩, h5⟩,
dsimp at *,
intro h1,
replace h1 := eq_of_zero_dist h1,
subst x,
unfold right,
dsimp,
unfold right_triple,
dsimp,
apply right_trans _ (eleven9 h5.1 (six5 h3)),
exact ⟨h5.1.2.1, h3, h5.2.2.symm.2.2.2.2 (six17a p b) (six17b b c)⟩
end

theorem thirteen6 {C D : dist point} {α : angle point} : ¬right α → cos α C = cos α D → C = D :=
begin
intros h h1,
by_cases h_1 : C = 0,
  subst C,
  rw [cos_times_zero] at h1,
  by_contradiction h_1,
  exact h (thirteen6a (ne.symm h_1) h1.symm),
by_cases h_2 : D = 0,
  subst D,
  rw [cos_times_zero] at h1,
  by_contradiction h_2,
  exact h (thirteen6a h_2 h1),
rcases quotient.exists_rep α with ⟨⟨⟨a, b, c⟩, h2, h3⟩, h4⟩,
rw ←h4 at *,
unfold right at h,
unfold cos cos_triple at h1,
dsimp at *,
unfold right_triple at h,
rw [dif_neg h_1, dif_neg h_2] at h1,
by_cases h_3 : col a b c,
  rwa [dif_pos h_3, dif_pos h_3] at h1,
rw [dif_neg h_3, dif_neg h_3] at h1,
rcases thirteen3 h_3 h_1 with ⟨⟨p, x⟩, h5⟩,
rcases thirteen3 h_3 h_2 with ⟨⟨q, y⟩, h6⟩,
dsimp at *,
intro h1,
have h7 : b ≠ x,
  intro h_4,
  subst x,
  apply h,
  apply right_trans _ (eleven9 h5.1 (six5 h3)),
  exact ⟨h5.1.2.1, h3, h5.2.2.symm.2.2.2.2 (six17a p b) (six17b b c)⟩,
have h8 : b ≠ y,
  intro h_4,
  subst y,
  exact h7 (id_eqd (quotient.exact h1)),
suffices : p = q,
  subst q,
  exact h5.2.1.symm.trans h6.2.1,
suffices : x = y,
  subst y,
  apply six21a (six14 h2) h5.2.2.2.1 _ (six4.1 h5.1).1 (six17a p x) (six4.1 h6.1).1 _,
    intro h_4,
    rw ←h_4 at h5,
    exact h7 (eight14d (eight15 ⟨x, h5.2.2⟩ (six17a b c) (six17b a b)) h5.2.2),
  rw unique_of_exists_unique (unique_xperp h5.2.2.1 h5.2.2.2.2.1) h5.2.2 h6.2.2,
  simp,
suffices : sided b x y,
  exact unique_of_exists_unique (six11 this.1 this.1) ⟨six5 this.1, eqd_refl b x⟩ ⟨this.symm, two5 (quotient.exact h1).symm⟩,
exact (thirteen8 (four11 (six4.1 (h5.1.symm.trans h6.1)).1).2.1 (six23.2 ⟨l b c, h5.2.2.1, six17a b c, h5.2.2.2.2.1, h6.2.2.2.2.1⟩) 
h7 h8 (h5.2.2.2.2.2.2 (six17a b c) (six17a p x)) (h6.2.2.2.2.2.2 (six17a b c) (six17a q y))).1 (h5.1.symm.trans h6.1)
end

end Euclidean_plane