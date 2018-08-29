import Euclid.tarski_4
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance] prop_decidable

-- Line Reflections

noncomputable def mid (a b : point) : point := classical.some (eight22 a b)

theorem ten1 (a b : point) : M a (mid a b) b := (classical.some_spec (eight22 a b)).1

@[simp] theorem mid.refl (a : point) : mid a a = a := (seven3.1 $ ten1 a a).symm

theorem mid.symm (a b : point) : mid a b = mid b a := seven17 (ten1 a b) (ten1 b a).symm

theorem midtoS (a b : point) : S (mid a b) a = b := (seven6 $ ten1 a b).symm

theorem midofS (a b : point) : mid b (S a b) = a := seven17 (ten1 b (S a b)) (seven5 a b)

theorem mid.neq {a b : point} : a ≠ b → mid a b ≠ a := --λ h h1, h ((seven11 a) ▸ h1 ▸ midtoS a b)
begin
intros h h1,
apply h,
suffices : eqd (mid a b) a (mid a b) b,
  rw h1 at this,
  exact id_eqd a b a this.symm,
exact (ten1 a b).2
end

theorem ten2 {p : point} {A : set point} (h : line A) (h_1 : p ∉ A) : ∃! q, mid p q ∈ A ∧ perp A (l p q) :=
begin
rcases h with ⟨a, b, h₁, h₂⟩,
rw h₂ at *,
cases eight18 h_1 with x hx,
apply exists_unique.intro (S x p),
  split,
    rw seven17 (ten1 p (S x p)) (seven5 x p),
    exact hx.1.1,
  apply (eight14f hx.1.2.symm (or.inl (seven5 x p).1) _).symm,
  intro h_2,
  have h1 : p = x := seven10.1 h_2.symm,
  subst x,
  exact h_1 hx.1.1,
intros y hy,
have h1 : p ≠ y,
  intro h_2,
  rw [←h_2, mid.refl p] at hy,
  exact h_1 hy.1,
have h2 := ten1 p y,
have h3 : mid p y = x,
  apply hx.2,
  refine ⟨hy.1,_⟩,
  suffices : l p y = l p (mid p y),
    rw ←this,
    exact hy.2,
  apply six18 (six14 h1),
      intro h_2,
      rw ←h_2 at h2,
      exact h1 (id_eqd p y p h2.2.symm),
    simp,
  right, left,
  exact h2.1.symm,
rw h3 at *,
exact unique_of_exists_unique (seven4 x p) h2 (seven5 x p)
end

noncomputable def Sl {A : set point} (h : line A) (a : point) : point := if h1 : a ∉ A then classical.some (ten2 h h1) else a

theorem ten3a {A : set point} (h : line A) {a : point} (h1 : a ∉ A) : mid a (Sl h a) ∈ A ∧ perp A (l a (Sl h a)) := begin
unfold Sl,
rw dif_pos h1,
exact (classical.some_spec (ten2 h h1)).1
end

theorem ten3b {A : set point} (h : line A) {a : point} (h1 : a ∈ A) : Sl h a = a := 
begin
unfold Sl,
have h2 : ¬a ∉ A,
  intro h_1,
  contradiction,
rw dif_neg h2
end

theorem Sl.symm {a b : point} (h : line (l a b)) (p : point) : Sl h p = Sl h.symm p :=
begin
cases em (p ∈ l a b),
  rw ten3b h h_1,
  suffices : p ∈ l b a,
    rw ten3b h.symm this,
  simpa [six17 a b] using h_1,
apply unique_of_exists_unique (ten2 h h_1),
  exact ten3a h h_1,
have h_2 : p ∉ l b a,
  rwa six17,
have h2 := ten3a h.symm h_2,
rwa six17 a b
end

theorem ten3c {A : set point} (h : line A) {a : point} : a ∉ A → Sl h a ∉ A :=
begin
intro h1,
have h2 := ten3a h h1,
cases em (a = Sl h a),
  rwa ←h_1,
intro h3,
apply h1,
have h4 := ten1 a (Sl h a),
suffices : A = l (Sl h a) (mid a (Sl h a)),
  rw this,
  left,
  exact h4.1.symm,
apply six18 h,
    intro h_2,
    apply h_1,
    rw ←h_2 at h4,
    exact id_eqd a (Sl h a) (Sl h a) h4.2.flip,
  exact h3,
exact h2.1
end

theorem ten3d {A : set point} (h : line A) (a : point) : Sl h a = S (mid a (Sl h a)) a :=
begin
exact (midtoS _ _).symm
end

theorem ten3e {A : set point} (h : line A) (a : point) : mid a (Sl h a) ∈ A :=
begin
cases em (a ∈ A),
  rw ten3b h h_1,
  simpa,
exact (ten3a h h_1).1
end

@[simp] theorem ten5 {A : set point} (h : line A) (a : point) : Sl h (Sl h a) = a := 
begin
cases em (a ∈ A),
  have h1 := ten3b h h_1,
  rwa h1,
have h1 := ten3a h h_1,
have h2 : Sl h a ∉ A,
  exact ten3c h h_1,
rw [mid.symm, six17] at h1,
apply unique_of_exists_unique (ten2 h h2),
  exact ten3a h h2,
exact h1
end

theorem ten4 {A : set point} {h : line A} {p q : point} : Sl h p = q ↔ Sl h q = p :=
begin
split;
{intro h1,
rw ←h1,
simp}
end

theorem ten6 {A : set point} (h : line A) (p : point) : ∃! q, Sl h q = p :=
begin
apply exists_unique.intro,
  exact ten5 h p,
intros y hy,
exact (ten4.1 hy).symm
end

theorem ten7 {A : set point} {h : line A} {p q : point} : Sl h p = Sl h q → p = q :=
begin
intro h1,
rw ←(ten4.1 h1),
simp
end

theorem ten8 {A : set point} (h : line A) {a : point} : Sl h a = a ↔ a ∈ A :=
begin
split,
  intro h1,
  by_contradiction h_1,
  apply h_1,
  have h2 := ten3a h h_1,
  rw h1 at *,
  simp at h2,
  exact h2.1,
intro h1,
exact ten3b h h1
end

theorem ten9 {A : set point} (h : line A) {a : point} : a ∉ A → perp A (l a (mid a (Sl h a))) :=
begin
intro h1,
have h2 := ten3a h h1,
suffices : l a (Sl h a) = l a (mid a (Sl h a)),
  rw ←this,
  exact h2.2,
have h3 : a ≠ Sl h a,
  intro h_1,
  apply h1,
  exact (ten8 h).1 h_1.symm,
have h4 := ten1 a (Sl h a),
apply six18 (six14 h3),
    intro h_1,
    apply h3,
    rw ←h_1 at h4,
    exact id_eqd a (Sl h a) a h4.2.symm,
  simp,
right, left,
exact h4.1.symm
end

theorem ten10 {A : set point} (h : line A) (p q : point) : eqd p q (Sl h p) (Sl h q) :=
begin
rw [ten3d h p, ten3d h q],
generalize h1 : mid p (Sl h p) = x,
generalize h2 : mid q (Sl h q) = y,
generalize h3 : mid x y = z,
have h4 := midtoS x y,
rw h3 at h4,
have h5 := seven5 x p,
have h6 := (seven14 z).1 h5,
rw h4 at h6,
have h7 := seven6 h6,
have h8 : eqd q (S z p) (S y q) (S z (S x p)),
  rw h7,
  apply seven13,
have h9 : R z x p,
  cases em (p ∈ A),
    rw (ten3b h h_1) at h1,
    simp at h1,
    subst p,
    simp,
  have h_2 : xperp x A (l p x),
    rw ←h1,
    exact eight15 (ten9 h h_1) (ten3e h p) (six17b p (mid p (Sl h p))),
  apply h_2.2.2.2.2,
    apply six27 h,
      exact ten3e h p,
      exact ten3e h q,
    rw [h1, h2, ←h3],
    exact (ten1 x y).1,
  simp,
have h10 : R z y q,
  cases em (q ∈ A),
    rw (ten3b h h_1) at h2,
    simp at h2,
    subst q,
    simp,
  have h_2 : xperp y A (l q y),
    rw ←h2,
    exact eight15 (ten9 h h_1) (ten3e h q) (six17b q (mid q (Sl h q))),
  apply h_2.2.2.2.2,
    apply six27 h,
      exact ten3e h q,
      exact ten3e h p,
    rw [h2, h1, ←h3],
    exact (ten1 x y).1.symm,
  simp,
unfold R at *,
have h11 : afs (S z p) z p q (S z (S x p)) z (S x p) (S y q),
  repeat {split},
    exact (seven5 z p).1.symm,
    exact (seven5 z (S x p)).1.symm,
    suffices : eqd (S z p) (S z z) (S z (S x p)) (S z z),
      simp at this,
      exact this,
    exact (seven16 z).1 h9.flip,
    exact h9,
    exact h8.flip,
  exact h10,
cases em (S z p = z),
  have h12 : p = z,
    exact seven9 (eq.trans h_1 (seven11 z).symm),
  have h13 : (S x p) = z,
    rw ←h12 at *,
    exact id_eqd (S x p) p p h9.symm.flip,
  exact h13.symm ▸ h12.symm ▸ h10,
exact afive_seg h11 h_1
end

theorem ten11a {A : set point} (h : line A) {a b c : point} : B a b c ↔ B (Sl h a) (Sl h b) (Sl h c) :=
begin
split,
  intro h1,
  apply four6 h1,
  repeat {split};
  exact ten10 h _ _,
intro h1,
rw ←ten5 h a,
rw ←ten5 h b,
rw ←ten5 h c,
apply four6 h1,
repeat {split};
exact ten10 h _ _
end

theorem ten11b {A : set point} (h : line A) {a b c d : point} : eqd a b c d ↔ eqd (Sl h a) (Sl h b) (Sl h c) (Sl h d) :=
begin
split,
  intro h1,
  exact (ten10 h a b).symm.trans (h1.trans (ten10 h c d)),
intro h1,
have h2 := (ten10 h (Sl h a) (Sl h b)).symm.trans (h1.trans (ten10 h (Sl h c) (Sl h d))),
simpa using h2
end

theorem ten12a {a b p : point} (h : line (l a b)) : R a b p → b = mid p (Sl h p) :=
begin
intro h1,
cases em (p ∈ l a b),
    cases eight9 h1 h_1,
    subst b,
    exfalso,
    exact six13a a h,
  subst p,
  suffices : Sl h b = b,
    rw this,
    simp,
  apply ten3b h (six17b a b),
suffices : S b p = Sl h p,
  rw ←this,
  exact (midofS b p).symm,
apply eq.symm,
apply unique_of_exists_unique (ten2 h h_1),
  exact ten3a h h_1,
split,
  rw midofS,
  simp,
have h3 : p ≠ b,
  intro h_2,
    apply h_1,
    subst p,
    simp,
suffices : l p (S b p) = l p b,
  rw this,
  suffices : xperp b (l a b) (l p b),
    constructor,
    exact this,
  apply eight13.2,
  split,
    exact h,
  split,
    exact six14 h3,
  split,
    simp,
  split,
    simp,
  existsi [a, p],
  split,
    simp,
  split,
    simp,
  split,
    exact six13 h,
  split,
    exact h3,
  exact h1,
apply six18 _ h3,
    simp,
  right, left,
  exact (seven5 b p).1.symm,
apply six14,
intro h_2,
apply h3,
exact (seven10.1 h_2.symm)
end

theorem ten12b {a b c : point} (h : line (l a b)) : R a b c → c = (Sl h (S b c)) :=
begin
intro h1,
have h2 : b = mid c (Sl h c),
  exact ten12a h h1,
suffices : S b c = Sl h c,
  rw this,
  simp,
suffices : S (mid c (Sl h c)) c = Sl h c,
  rwa ←h2 at this,
exact midtoS c (Sl h c)
end

theorem ten12c {a b c a' : point} : R a b c → R a' b c → eqd a b a' b → eqd a c a' c :=
begin
intros h h1 h2,
generalize h3 : mid a a' = z,
have h4 : R b z a,
  unfold R,
  rw ←h3,
  rw midtoS,
  exact h2.flip,
cases em (b = c),
  subst b,
  exact h2,
cases em (b = z),
  subst z,
  have h5 := six14 (ne.symm h_1),
  have h6 : a' = Sl h5 a,
    suffices : a = S b a',
      rw this,
      exact ten12b h5 h1.symm,
    rw [h_2, mid.symm],
    exact (midtoS a' a).symm,
  have h7 : c = Sl h5 c,
    suffices : c ∈ l c b,
      exact (ten3b h5 this).symm,
    simp,
  rw h6,
  simpa [h7.symm] using (ten10 h5 a c),
have h5 := six14  h_2,
have h6 : a = (Sl h5 a'),
  rw [(midtoS a a').symm, h3],
  exact ten12b h5 h4,
have h7 : b = Sl h5 b,
  suffices : b ∈ l b z,
      exact (ten3b h5 this).symm,
    simp,
have h8 : eqd a c a (S b c),
  unfold R at h,
  exact h,
cases em (a = a'),
  subst a',
  exact eqd.refl a c,
have h9 : R z b c,
  unfold R,
  apply four17 h_3,
      rw ←h3,
      right, left,
      exact (ten1 a a').1.symm,
    exact h8,
  unfold R at h1,
  exact h1,
have h10 : (S b c) = Sl h5 c,
  rw Sl.symm,
  rw ten4.1,
  apply eq.symm,
  exact ten12b _ h9,
apply h8.trans,
apply eqd.symm,
rw [h6, h10],
exact ten10 h5 a' c
end

theorem ten12 {a b c a' b' c' : point} : R a b c → R a' b' c' → eqd a b a' b' → eqd b c b' c' → eqd a c a' c' :=
begin
intros h h1 h2 h3,
generalize h4 : mid b b' = x,
have h5 : b = S x b',
  rw [←h4, mid.symm],
  apply eq.symm,
  exact midtoS b' b,
have h6 : cong a' b' c' (S x a') b (S x c'),
  rw h5,
  exact seven16a x,
have h7 : R (S x a') b (S x c'),
  exact eight10 h1 h6,
apply eqd.trans _ h6.2.2.symm,
generalize h8 : mid c (S x c') = y,
have h9 : R b y c,
  unfold R,
  rw ←h8,
  rw midtoS,
  exact h3.trans h6.2.1,
cases em (b = y),
  subst y,
  have h10 : (S b (S x c')) = c,
    rw [h_1, mid.symm],
    exact midtoS (S x c') c,
  have h11 : cong (S x a') b (S x c') (S b (S x a')) b c,
    rw ←h10,
    suffices : cong (S x a') b (S x c') (S b (S x a')) (S b b) (S b (S x c')),
      simpa [this],
    exact seven16a b,
  apply eqd.trans _ h11.2.2.symm,
  apply ten12c h,
    exact eight10 h7 h11,
  exact h2.trans (h6.1.trans h11.1),
have h10 := six14 h_1,
have h11 : c = Sl h10 (S x c'),
  rw [←midtoS c (S x c'), h8],
  exact ten12b h10 h9,
have h12 : b = Sl h10 b,
  suffices : b ∈ l b y,
    exact (ten3b h10 this).symm,
  simp,
have h13 : cong (S x a') b (S x c') (Sl h10 (S x a')) (Sl h10 b) (Sl h10 (S x c')),
  repeat {split};
  exact ten10 h10 _ _,
rw [←h11, ←h12] at h13,
apply eqd.trans _ h13.2.2.symm,
exact ten12c h (eight10 h7 h13) (h2.trans (h6.1.trans h13.1))
end

theorem ten14 {A : set point} (h : line A) {a : point} : a ∉ A → Bl a A (Sl h a) :=
begin
intro h1,
split,
  exact h,
split,
  exact h1,
split,
  exact ten3c h h1,
constructor,
split,
  exact (ten3a h h1).1,
exact (ten1 a (Sl h a)).1
end

theorem ten15 {A : set point} (h : line A) {a q : point} : a ∈ A → q ∉ A → ∃ p, perp A (l p a) ∧ side A p q :=
begin
intros h1 h2,
cases six22 h h1 with b hb,
cases nine10 h h2 with c hc,
rcases eight21 hb.1 c with ⟨p, t, ht⟩,
existsi p,
split,
  rw hb.2,
  exact ht.1,
existsi c,
split,
  split,
    exact h,
  split,
    intro h_1,
    apply eight14a ht.1,
    apply six18,
          rwa hb.2 at h,
        exact six13 (eight14e ht.1).2,
      rwa hb.2 at h_1,
    simp,
  split,
    exact hc.2.2.1,
  existsi t,
  split,
    rw hb.2,
    exact ht.2.1,
  exact ht.2.2.symm,
exact hc
end

theorem ten16 {a b c p a' b' : point} : ¬col a b c → ¬col a' b' p → eqd a b a' b' → ∃! c', cong a b c a' b' c' ∧ side (l a' b') c' p :=
begin
intros h h1 h2,
apply exists_unique_of_exists_of_unique,
  cases eight18 h with x hx,
  cases four14 hx.1.1 h2 with x' hx',
  have h3 : col a' b' x',
    exact four13 hx.1.1 hx',
  cases ten15 (six14 (six26 h1).1) h3 h1 with q hq,
  have h4 : x ≠ c,
    intro h_1,
    subst x,
    exact h hx.1.1,
  cases six11 (six13 (eight14e hq.1).2) h4 with c' hc',
  constructor,
  have h5 : cong a b c a' b' c',
    split,
      exact h2,
    have h5 : xperp x (l a b) (l c x),
      exact eight15 hx.1.2 hx.1.1 (six17b c x),
    have h6 : xperp x' (l a' b') (l c' x'),
      suffices : perp (l a' b') (l c' x'),
        exact eight15 this h3 (six17b c' x'),
      suffices : l q x' = l c' x',
        rw this at hq,
        exact hq.1,
      apply six18 (eight14e hq.1).2,
          intro h_1,
          apply h4,
          subst c',
          exact id_eqd x c x' hc'.1.2.symm,          
        exact (four11 (six4.1 hc'.1.1).1).2.2.2.2,
      simp,
    split,
      have h7 : R b x c,
        simp [h5.2.2.2.2 b c],    
      have h8 : R b' x' c',
        simp [h6.2.2.2.2 b' c'],
      exact ten12 h7 h8 hx'.2.1 hc'.1.2.symm,
    have h7 : R a x c,
        simp [h5.2.2.2.2 a c],    
    have h8 : R a' x' c',
      simp [h6.2.2.2.2 a' c'],
    exact ten12 h7 h8 hx'.2.2 hc'.1.2.symm,
  split,
    exact h5,
  apply side.trans _ hq.2,
  apply (nine19 (six14 (six26 h1).1) h3 (four11 (six4.1 hc'.1.1).1).1).2,
  split,
    exact hc'.1.1,
  intro h_1,
  exact h (four13 h_1 h5.symm),
intros c' c'' hc' hc'',
have h3 := hc'.1.symm.trans hc''.1,
have h4 := hc'.2.trans hc''.2.symm,
have h5 := six14 (six26 h1).1,
generalize h6 : Sl h5 c'' = c₁,
have h7 : Bl c'' (l a' b') c₁,
  rw ←h6,
  exact ten14 h5 (nine11 h4).2.2,
have h8 : Bl c' (l a' b') c₁,
  exact (nine8 h7).2 h4.symm,
cases h8.2.2.2 with t ht,
have h9 : cong a' b' c' a' b' c₁,
  apply h3.trans,
  have h_1 : a' = Sl h5 a',
    apply (ten3b h5 _).symm,
    simp,
  have h_2 : b' = Sl h5 b',
    apply (ten3b h5 _).symm,
    simp,
  have h_3 : cong a' b' c'' (Sl h5 a') (Sl h5 b') c₁,
    rw ←h6,
    repeat {split};
    exact ten10 h5 _ _,
  simpa [h_2.symm, h_1.symm] using h_3,
have h10 : c₁ = S t c',
  suffices : M c' t c₁,
    exact unique_of_exists_unique (seven4 t c') this (seven5 t c'),
  split,
    exact ht.2,
  exact four17 (six26 h1).1 ht.1 h9.2.2 h9.2.1,
suffices : Sl h5 c' = c₁,
  exact ten7 (this.trans h6.symm),
apply unique_of_exists_unique (ten2 h5 h8.2.1),
  exact ten3a h5 h8.2.1,
split,
  rw [h10, midofS],
  exact ht.1,
existsi t,
apply eight13.2,
split,
  exact six14 (six26 h1).1,
split,
  exact six14 (nine2 h8),
split,
  exact ht.1,
split,
  right, left,
  exact ht.2.symm,
cases em (a' = t),
  have h_2 : b' ≠ t,
    intro h_2,
    exact (six26 h1).1 (h_1.trans h_2.symm),
  existsi [b', c'],
  split,
    simp,
  split,
    simp,
  split,
    exact h_2,
  split,
    intro h_3,
    subst h_3,
    exact h8.2.1 ht.1,
  unfold R,
  rw ←h10,
  exact h9.2.1,  
existsi [a', c'],
split,
  simp,
split,
  simp,
split,
  exact h_1,
split,
  intro h_1,
  subst t,
  exact h8.2.1 ht.1,
unfold R,
rw ←h10,
exact h9.2.2
end

-- Angles

def eqa (a b c d e f : point) : Prop := a ≠ b ∧ c ≠ b ∧ d ≠ e ∧ f ≠ e ∧ ∃ a' c' d' f',
B b a a' ∧ eqd a a' e d ∧ B b c c' ∧ eqd c c' e f ∧ B e d d' ∧ eqd d d' b a ∧ B e f f' ∧ eqd f f' b c ∧ eqd a' c' d' f'

theorem eleven3a {a b c d e f : point} : eqa a b c d e f → ∃ a' c' d' f', sided b a' a ∧ 
sided b c' c ∧ sided e d' d ∧ sided e f' f ∧ cong a' b c' d' e f' :=
begin
unfold eqa,
intro h,
rcases h.2.2.2.2 with ⟨a', c', d', f', h1⟩,
existsi [a', c', d', f'],
split,
  exact (six7 h1.1 h.1).symm,
split,
  exact (six7 h1.2.2.1 h.2.1).symm,
split,
  exact (six7 h1.2.2.2.2.1 h.2.2.1).symm,
split,
  exact (six7 h1.2.2.2.2.2.2.1 h.2.2.2.1).symm,
split,
  exact two5 (two11 h1.1.symm h1.2.2.2.2.1 (two4 h1.2.1) (two4 h1.2.2.2.2.2.1.symm)),
split,
  exact two5 (two11 h1.2.2.1 h1.2.2.2.2.2.2.1.symm (two5 h1.2.2.2.2.2.2.2.1.symm) (two5 h1.2.2.2.1)),
exact h1.2.2.2.2.2.2.2.2
end

theorem eleven4a {a b c d e f : point} : (∃ a' c' d' f', sided b a' a ∧ sided b c' c ∧ sided e d' d ∧ sided e f' f ∧ cong a' b c' d' e f') → a ≠ b ∧ c ≠ b ∧ d ≠ e ∧ f ≠ e ∧
∀ a' c' d' f', sided b a' a → sided b c' c → sided e d' d → sided e f' f → eqd b a' e d' → eqd b c' e f' → eqd a' c' d' f' :=
begin
intro h,
rcases h with ⟨a', c', d', f', h1⟩,
repeat {split},
        exact h1.1.2.1,
      exact h1.2.1.2.1,
    exact h1.2.2.1.2.1,
  exact h1.2.2.2.1.2.1,
intros a1 c1 d1 f1 h2 h3 h4 h5 h6 h7,
have h8 : cong b a' a1 e d' d1,
  exact six10 (h1.1.trans h2.symm) (h1.2.2.1.trans h4.symm) h1.2.2.2.2.1.flip h6,
have h9 : eqd a1 c' d1 f',
  suffices : fs b a' a1 c' e d' d1 f',
    exact four16 this h1.1.1.symm,
  repeat {split},
            exact (four11 (six4.1 (h1.1.trans h2.symm)).1).2.1,
          exact h8.1,
        exact h8.2.1,
      exact h8.2.2,
    exact h1.2.2.2.2.2.1,
  exact h1.2.2.2.2.2.2,
suffices : fs b c' c1 a1 e f' f1 d1,
  exact (four16 this h1.2.1.1.symm).flip,
repeat {split},
          exact (four11 (six4.1 (h1.2.1.trans h3.symm)).1).2.1,
        exact h1.2.2.2.2.2.1,
      exact (six10 (h1.2.1.trans h3.symm) (h1.2.2.2.1.trans h5.symm) h1.2.2.2.2.2.1 h7).2.1,
    exact h7,
  exact h6,
exact h9.flip
end

theorem eleven2a {a b c d e f : point} : (a ≠ b ∧ c ≠ b ∧ d ≠ e ∧ f ≠ e ∧ 
∀ a' c' d' f', sided b a' a → sided b c' c → sided e d' d → sided e f' f → eqd b a' e d' → eqd b c' e f' → eqd a' c' d' f') → 
eqa a b c d e f :=
begin
intro h,
unfold eqa,
split,
  exact h.1,
split,
  exact h.2.1,
split,
  exact h.2.2.1,
split,
  exact h.2.2.2.1,
cases seg_cons a e d b with a' ha',
cases seg_cons c e f b with c' hc',
cases seg_cons d b a e with d' hd',
cases seg_cons f b c e with f' hf',
existsi [a', c', d', f'],
repeat {split},
                exact ha'.1,
              exact ha'.2,
            exact hc'.1,
          exact hc'.2,
        exact hd'.1,
      exact hd'.2,
    exact hf'.1,
  exact hf'.2,
apply h.2.2.2.2 a' c' d' f',
          exact (six7 ha'.1 h.1).symm,
        exact (six7 hc'.1 h.2.1).symm,
      exact (six7 hd'.1 h.2.2.1).symm,
    exact (six7 hf'.1 h.2.2.2.1).symm,
  exact two5 (two11 ha'.1 hd'.1.symm (two5 hd'.2.symm) (two5 ha'.2)),
exact two5 (two11 hc'.1 hf'.1.symm (two5 hf'.2.symm) (two5 hc'.2))
end

theorem eleven3 {a b c d e f : point} : eqa a b c d e f ↔ ∃ a' c' d' f', sided b a' a ∧ 
sided b c' c ∧ sided e d' d ∧ sided e f' f ∧ cong a' b c' d' e f' :=
⟨λ h, eleven3a h, λ h, eleven2a (eleven4a h)⟩

theorem eleven4 {a b c d e f : point} : eqa a b c d e f ↔ a ≠ b ∧ c ≠ b ∧ d ≠ e ∧ f ≠ e ∧
∀ a' c' d' f', sided b a' a → sided b c' c → sided e d' d → sided e f' f → eqd b a' e d' → eqd b c' e f' → eqd a' c' d' f' :=
⟨λ h, eleven4a (eleven3a h), λ h, eleven2a h⟩

lemma eleven5 {a b c d e f : point} : eqa a b c d e f ↔ ∃ d' f', sided e d' d ∧ sided e f' f ∧ cong a b c d' e f' :=
begin
split,
  intro h,
  cases exists_of_exists_unique (six11 h.2.2.1 h.1.symm) with d' hd,
  cases exists_of_exists_unique (six11 h.2.2.2.1 h.2.1.symm) with f' hf,
  refine ⟨d', f', hd.1, hf.1, _⟩,
  exact ⟨hd.2.symm.flip, hf.2.symm, (eleven4.1 h).2.2.2.2 a c d' f' (six5 h.1) (six5 h.2.1) hd.1 hf.1 hd.2.symm hf.2.symm⟩,
rintros ⟨d', f', h, h1, h2⟩,
apply eleven3.2 ⟨a, c, d', f', _, _, h, h1, h2⟩,
  exact six5 (two7 h2.1.symm h.1),
exact six5 (two7 h2.2.1.symm.flip h1.1)
end

theorem eqa.refl {a b c : point} : a ≠ b → c ≠ b → eqa a b c a b c :=
begin
intros h h1,
rw eleven3,
existsi [a, c, a, c],
simp [six5 h, six5 h1]
end

theorem eqa.symm {a b c d e f : point} : eqa a b c d e f → eqa d e f a b c :=
begin
unfold eqa,
rintros ⟨h, h1, h2, h3, a', c', d', f', h4, h5, h6, h7, h8, h9, h10, h11, h12⟩,
simp [*, -exists_and_distrib_left],
existsi [d', f', a', c'],
simp [*, h12.symm]
end

theorem eqa.trans {a b c d e f p q r : point} : eqa a b c d e f → eqa d e f p q r → eqa a b c p q r :=
begin
intros h g,
have h1 := h,
rw eleven3 at h1,
rcases h1 with ⟨a', c', d', f', h1, h2, h3, h4, h5, h6, h7⟩,
rw eleven4 at g,
cases seg_cons a' p q b with a₁ ha,
cases seg_cons c' r q b with c₁ hc,
cases seg_cons d' p q e with d₁ hd,
cases seg_cons f' r q e with f₁ hf,
cases seg_cons p d' e q with p₁ hp,
cases seg_cons r f' e q with r₁ hr,
have h8 : eqd b a₁ e d₁,
  exact two11 ha.1 hd.1 h5.flip (ha.2.trans hd.2.symm),
have h9 : eqd b c₁ e f₁,
  exact two11 hc.1 hf.1 h6 (hc.2.trans hf.2.symm),
have h10 : eqd e d₁ q p₁,
  exact two5 (two11 hd.1 hp.1.symm hp.2.symm.flip hd.2),
have h11 : eqd e f₁ q r₁,
  exact two5 (two11 hf.1 hr.1.symm hr.2.symm.flip hf.2),
have h12 : sided b a₁ a,
  exact six7a ha.1 h1,
have h13 : sided b c₁ c,
  exact six7a hc.1 h2,
have h14 : sided e d₁ d,
  exact six7a hd.1 h3,
have h15 : sided e f₁ f,
  exact six7a hf.1 h4,
have h16 : sided q p₁ p,
  exact (six7 hp.1 g.2.2.1).symm,
have h17 : sided q r₁ r,
  exact (six7 hr.1 g.2.2.2.1).symm,
have h18 := g.2.2.2.2 d₁ f₁ p₁ r₁ h14 h15 h16 h17 h10 h11,
rw eleven3,
existsi [a₁, c₁, p₁, r₁],
simp *,
split,
  exact (h8.trans h10).flip,
split,
  exact h9.trans h11,
apply eqd.trans _ h18,
rw eleven4 at h,
exact h.2.2.2.2 a₁ c₁ d₁ f₁ h12 h13 h14 h15 h8 h9
end

theorem eleven6 {a b c : point} : a ≠ b → c ≠ b → eqa a b c c b a :=
begin
intros h h1,
cases seg_cons a c b b with a' ha,
cases seg_cons c a b b with c' hc,
rw eleven3,
existsi [a', c', c', a'],
simp [(six7 ha.1 h).symm, (six7 hc.1 h1).symm],
unfold cong,
have h3 : eqd b a' c' b,
  exact two11 ha.1 hc.1.symm hc.2.symm.flip ha.2,
split,
  exact two4 h3,
split,
  exact two4 h3.symm,
exact two5 (eqd.refl a' c')
end

theorem eleven7 {a b c d e f : point} : eqa a b c d e f → eqa c b a d e f :=
λ h, (eleven6 h.1 h.2.1).symm.trans h

theorem eleven8 {a b c d e f : point} : eqa a b c d e f → eqa a b c f e d :=
λ h, h.trans (eleven6 h.2.2.1 h.2.2.2.1)

theorem eqa.flip {a b c d e f : point} : eqa a b c d e f → eqa c b a f e d :=
λ h, eleven8 (eleven7 h)

theorem eleven9 {a b c a' c' : point} : sided b a' a → sided b c' c → eqa a b c a' b c' :=
begin
intros h h1,
rw eleven3,
existsi [a', c', a', c'],
simp [h, h1, six5 h.1, six5 h1.1]
end

theorem eleven10 {a b c d e f a' c' d' f' : point} : eqa a b c d e f → sided b a' a → sided b c' c → 
sided e d' d → sided e f' f → eqa a' b c' d' e f' :=
begin
intros h h1 h2 h3 h4,
exact (eleven9 h1 h2).symm.trans (h.trans (eleven9 h3 h4))
end

theorem eleven11 {a b c d e f : point} : a ≠ b → c ≠ b → cong a b c d e f → eqa a b c d e f :=
λ h h1 h2, eleven3.2 ⟨a, c, d, f, (six5 h), (six5 h1), (six5 (two7 h2.1 h)), (six5 (two7 h2.2.1.flip h1)), h2⟩

theorem eleven12 {a b c : point} (p : point): a ≠ b → c ≠ b → eqa a b c (S p a) (S p b) (S p c) :=
begin
intros h h1,
rw eleven3,
existsi [a, c, (S p a), (S p c)],
simp [six5 h, six5 h1, six5 (seven9a p h), six5 (seven9a p h1), seven16a p]
end

theorem eleven13 {a b c d e f a' d' : point} : eqa a b c d e f → a' ≠ b → B a b a' → d' ≠ e → B d e d' → eqa a' b c d' e f :=
begin
intros h h1 h2 h3 h4,
rw eleven3 at h,
rcases h with ⟨a₁, c₁, d₁, f₁, h⟩,
suffices : eqa (S b a₁) b c (S e d₁) e f,
  apply eleven10 this,
        split,
          exact h1,
        split,
          exact this.1,
        suffices : B a b (S b a₁),
          exact five2 h.1.2.1 h2 this,
        exact (six6 (seven5 b a₁).1.symm h.1).symm,
      exact six5 h.2.1.2.1,
    split,
      exact h3,
    split,
      exact this.2.2.1,
    suffices : B d e (S e d₁),
      exact five2 h.2.2.1.2.1 h4 this,
    exact (six6 (seven5 e d₁).1.symm h.2.2.1).symm,
  exact six5 h.2.2.2.1.2.1,
rw eleven3,
existsi [(S b a₁), c₁, (S e d₁), f₁],
simp [six5 (seven12 h.1.1.symm).symm, h.2.1, six5 (seven12 h.2.2.1.1.symm).symm, h.2.2.2.1],
split,
  exact (seven5 b a₁).2.symm.flip.trans (h.2.2.2.2.1.trans (seven5 e d₁).2.flip),
split,
  exact h.2.2.2.2.2.1,
suffices : afs a₁ b (S b a₁) c₁ d₁ e (S e d₁) f₁,
  exact afive_seg this h.1.1,
repeat {split},
          exact (seven5 b a₁).1,
        exact (seven5 e d₁).1,
      exact h.2.2.2.2.1,
    exact (seven5 b a₁).2.symm.trans (h.2.2.2.2.1.flip.trans (seven5 e d₁).2),
  exact h.2.2.2.2.2.2,
exact h.2.2.2.2.2.1
end

theorem eleven14 {a b c a' c' : point} : a ≠ b → c ≠ b → a' ≠ b → c' ≠ b → B a b a' → B c b c' → eqa a b c a' b c' :=
begin
intros h h1 h2 h3 h4 h5,
apply (eleven12 b h h1).trans,
simp,
suffices : sided b a' (S b a) ∧ sided b c' (S b c),
  exact eleven9 this.1 this.2,
split,
  apply six3.2,
  split,
    exact h2,
  split,
    exact (seven12 h.symm).symm,
  existsi a,
  split,
    exact h,
  split,
    exact h4.symm,
  exact (seven5 b a).1.symm,
apply six3.2,
split,
  exact h3,
split,
  exact (seven12 h1.symm).symm,
existsi c,
split,
  exact h1,
split,
  exact h5.symm,
exact (seven5 b c).1.symm
end

theorem eleven15a {a b c d e p : point} : ¬col a b c → ¬col d e p → ∃ f, eqa a b c d e f ∧ side (l e d) f p :=
begin
intros h h1,
cases exists_of_exists_unique (six11 (six26 h1).1 (six26 h).1.symm) with d' hd,
have h2 : ¬col d' e p,
  intro h_1,
  have h_2 := (six4.1 hd.1).1,
  exact (four10 h1).2.2.1 (five4 hd.1.1.symm (four11 h_1).2.1 (four11 h_2).2.1),
cases ten16 h h2 hd.2.symm.flip with f hf,
dsimp at hf,
existsi f,
split,
  rw eleven3,
  existsi [a, c, d', f],
  simp [six5 (six26 h).1, six5 (six26 h).2.1.symm, hd.1, hf.1.1],
  apply six5,
  intro h_1,
  subst f,
  exact (six26 h).2.1 (id_eqd b c e hf.1.1.2.1),
have h3 : l e d = l d' e,
  exact six18 (six14 (six26 h1).1.symm) hd.1.1 (four11 (six4.1 hd.1).1).2.2.1 (six17a e d),
rw h3,
exact hf.1.2
end

theorem eleven15b {a b c d e p : point} : ¬col a b c → ¬col d e p → ∀ f1 f2, eqa a b c d e f1 → 
side (l e d) f1 p → eqa a b c d e f2 → side (l e d) f2 p → sided e f1 f2 :=
begin
intros h h1 f1 f2 h2 h3 h4 h5,
cases exists_of_exists_unique (six11 (six26 h1).1 (six26 h).1.symm) with d' hd,
have h6 : ¬col d' e p,
  intro h_1,
  have h_2 := (six4.1 hd.1).1,
  exact (four10 h1).2.2.1 (five4 hd.1.1.symm (four11 h_1).2.1 (four11 h_2).2.1),
cases ten16 h h6 hd.2.symm.flip with f hf,
dsimp at hf,
have h7 : f1 ≠ e,
  intro h_1,
  subst f1,
  exact (nine11 h3).2.1 (six17a e d),
have h8 : f2 ≠ e,
  intro h_1,
  subst f2,
  exact (nine11 h5).2.1 (six17a e d),
cases exists_of_exists_unique (six11 h7 (six26 h).2.1) with f₁ h9,
cases exists_of_exists_unique (six11 h8 (six26 h).2.1) with f₂ h10,
have h11 : cong a b c d' e f₁,
  split,
    exact hf.1.1.1,
  split,
    exact h9.2.symm,
  suffices : eqa a b c d' e f₁,
    apply (eleven4.1 this).2.2.2.2 a c d' f₁ (six5 (six26 h).1) (six5 (six26 h).2.1.symm) (six5 hd.1.1) (six5 h9.1.1),
      exact hf.1.1.1.flip,
    exact h9.2.symm,
  exact h2.trans (eleven9 hd.1 h9.1),
have h12 : cong a b c d' e f₂,
  split,
    exact hf.1.1.1,
  split,
    exact h10.2.symm,
  suffices : eqa a b c d' e f₂,
    apply (eleven4.1 this).2.2.2.2 a c d' f₂ (six5 (six26 h).1) (six5 (six26 h).2.1.symm) (six5 hd.1.1) (six5 h10.1.1),
      exact hf.1.1.1.flip,
    exact h10.2.symm,
  exact h4.trans (eleven9 hd.1 h10.1),
have h13 : l e d = l d' e,
  exact six18 (six14 (six26 h1).1.symm) hd.1.1 (four11 (six4.1 hd.1).1).2.2.1 (six17a e d),
have h14 : side (l d' e) f₁ p,
  rw h13 at *,
  apply (nine19a h3 (six17b d' e) h9.1),
have h15 : side (l d' e) f₂ p,
  rw h13 at *,
  apply (nine19a h5 (six17b d' e) h10.1),
have h16 : f₁ = f,
  apply hf.2,
  split,
    exact h11,
  exact h14,
subst f₁,
have h16 : f₂ = f,
  apply hf.2,
  split,
    exact h12,
  exact h15,
subst f₂,
exact h9.1.symm.trans h10.1
end

theorem eleven15c {a b c x : point} : eqa a b c a b x → side (l a b) c x → sided b c x :=
begin
intros h h1,
have h2 : ¬col a b c,
  exact (nine11 h1).2.1,
apply eleven15b h2 h2 c x (eqa.refl (six26 h2).1 (six26 h2).2.1.symm) (side.refla (four10 h2).2.1) h,
rwa six17,
exact h1.symm
end

theorem eleven16 {a b c a' b' c' : point} : a ≠ b → c ≠ b → a' ≠ b' → c' ≠ b' → R a b c → R a' b' c' → 
eqa a b c a' b' c' :=
begin
intros h h1 h2 h3 h4 h5,
cases exists_of_exists_unique (six11 h2 h.symm) with a₁ ha,
cases exists_of_exists_unique (six11 h3 h1.symm) with c₁ hc,
rw eleven3,
existsi [a, c, a₁, c₁],
simp [six5 h, six5 h1, ha.1, hc.1],
refine ⟨ha.2.symm.flip, hc.2.symm, _⟩,
apply ten12 h4,
    suffices : R a' b' c₁,
      apply eight3 this h2,
      exact (four11 (six4.1 ha.1).1).2.2.1,
    apply R.symm,
    apply eight3 h5.symm h3,
    exact (four11 (six4.1 hc.1).1).2.2.1,
  exact ha.2.symm.flip,
exact hc.2.symm
end

theorem eleven17 {a b c a' b' c' : point} : R a b c → eqa a b c a' b' c' → R a' b' c' :=
begin
intros h h1,
rcases eleven5.1 h1 with ⟨a₁, c₁, ha, hc, h2⟩,
apply eight3 _ ha.1 (four11 (six4.1 ha).1).2.1,
exact (eight3 (eight10 h h2).symm hc.1 (four11 (six4.1 hc).1).2.1).symm
end

theorem eleven18 {a b c d : point} : B c b d → c ≠ b → d ≠ b → a ≠ b → (R a b c ↔ eqa a b c a b d) :=
begin
intros h h1 h2 h3,
split,
  intro h4,
  have h5 : R a b d,
    apply (eight3 h4.symm h1 _).symm,
    right, right,
    exact h.symm,
  exact eleven16 h3 h1 h3 h2 h4 h5,
intro h4,
rw eleven3 at h4,
rcases h4 with ⟨a', c', a₁, d', h4⟩,
have : a₁ = a',
  apply unique_of_exists_unique (six11 h3 h4.2.2.1.1.symm),
    split,
      exact h4.2.2.1,
    exact eqd.refl b a₁,
  split,
    exact h4.1,
  exact h4.2.2.2.2.1.flip,
subst a₁,
have : d' = (S b c'),
  apply unique_of_exists_unique (two12 b b c' c' h4.2.1.1),
    split,
      exact six8 h4.2.1 h4.2.2.2.1 h,
    exact h4.2.2.2.2.2.1.symm,
  split,
    exact (seven5 b c').1,
  exact (seven5 b c').2.symm,
subst d',
have h5 : R a' b c',
  unfold R,
  exact h4.2.2.2.2.2.2,
exact eleven17 h5 (eleven9 h4.1.symm h4.2.1.symm)
end

theorem eleven19 {a b p q : point} : R b a p → R b a q → side (l a b) p q → sided a p q :=
begin
intros h h1 h2,
have h3 : ¬col b a p,
  exact (four10 (nine11 h2).2.1).2.1,
have h4 : ¬col b a q,
  exact (four10 (nine11 h2).2.2).2.1,
apply (eleven15b h3 h3),
      exact eqa.refl (six26 h3).1 (six26 h3).2.1.symm,
    exact side.refl (nine11 h2).1 (nine11 h2).2.1,
  exact eleven16 (six26 h3).1 (six26 h3).2.1.symm (six26 h4).1 (six26 h4).2.1.symm h h1,
exact h2.symm
end

theorem eleven20 {a : point} {A P : set point} : line A → plane P → a ∈ A → A ⊆ P → ∃! B, B ⊆ P ∧ xperp a A B :=
begin
intros h h1 h2 h3,
cases six22 h h2 with b hb,
cases (nine25 h1 (h3 h2) _ hb.1 ).2 with x hx,
  show b ∈ P,
  apply h3,
  rw hb.2,
  simp,
rw hb.2 at *,
have h4 : x ∉ l a b,
  apply nine28 (six14 hb.1),
  rwa hx at h1,
cases ten15 h h2 h4 with c hc,
have h5 : c ∈ P,
  rw hx,
  left,
  exact hc.2,
apply exists_unique.intro (l c a),
  split,
    exact (nine25 h1 h5 (h3 h2) (six13 (eight14e hc.1).2)).1,
  exact eight15 hc.1 (six17a a b) (six17b c a),
intros Y h6,
have h7 : c ∉ l a b,
  intro h_1,
  apply eight14a hc.1,
  exact six18 (six14 hb.1) (six13 (eight14e hc.1).2) h_1 (six17a a b),
have h8 : P = planeof a b c,
  apply nine26 h7 h1 _ _ h5,
    exact h3 (six17a a b),
  exact h3 (six17b a b),
cases (six22 h6.2.2.1 h6.2.2.2.2.1) with y hy,
have h9 : R b a c,
  exact (eight15 hc.1 (six17a a b) (six17b c a)).2.2.2.2 b c (six17b a b) (six17a c a),
rw h8 at h6,
have h10 : y ∈ Y,
  rw hy.2,
  simp,
have h11 : R b a y,
  exact h6.2.2.2.2.2 b y (six17b a b) h10,
rw hy.2 at *,
cases (h6.1 h10),
  have h12 : sided a c y,
    exact eleven19 h9 h11 h_1.symm,
  exact six18 (six14 hy.1) (six13 (eight14e hc.1).2) (four11 (six4.1 h12).1).2.2.1 (six17a a y),
cases h_1,
  exfalso,
  apply (eight14b h6.2),
  exact six18 h hy.1 (six17a a b) h_1,
have h12 := six14 hb.1,
have h13 : side (l a b) y (Sl h12 c),
  exact (nine8 h_1.symm).1 (ten14 h12 h7).symm,
have h14 : side (l a b) y (S a c),
  have h_2 : S a c = Sl h12 c,
    have h_3 := ten12b h12.symm h9.flip,
    rw Sl.symm at h_3,
    simpa using h_3,
  rwa h_2,
apply eq.symm,
apply six18 (eight14e hc.1).2 hy.1 (six17b c a) (or.inl $ six6 (seven5 a c).1 (eleven19 h11 h9.flip h14).symm)
end


theorem eleven21a {a b c a' b' c' : point} (h : sided b a c) : eqa a b c a' b' c' ↔ sided b' a' c' :=
begin
split,
  intro h1,
    rcases eleven5.1 h1 with ⟨a₁, c₁, ha, hc, h2⟩,
    suffices : sided b' a₁ c₁,
      exact ha.symm.trans (this.trans hc),
    apply six10a h ⟨h2.1.flip, _, h2.2.1⟩,
    exact (eleven4.1 h1).2.2.2.2 a c a₁ c₁ (six5 h1.1) (six5 h1.2.1) ha hc h2.1.flip h2.2.1,
intro h1,
cases exists_of_exists_unique (six11 h1.1 h.1.symm) with a₁ ha,
apply eleven3.2 ⟨a, a, a₁, a₁, _ ⟩,
simp [six5 h.1, h, ha.1, ha.1.trans h1],
exact ⟨ha.2.symm.flip, ha.2.symm, two8 a a₁⟩
end

theorem eleven21b {a b c a' b' c' : point} : B a b c → eqa a b c a' b' c' → B a' b' c' :=
begin
intros h h1,
rcases eleven5.1 h1 with ⟨a₁, c₁, ha, hc, h2⟩,
exact six8 ha.symm hc.symm (four6 h h2)
end

theorem eleven21c {a b c a' b' c' : point} : a ≠ b → c ≠ b → a' ≠ b' → c' ≠ b' → B a b c → B a' b' c' → eqa a b c a' b' c' :=
begin
intros h h1 h2 h3 h4 h5,
cases exists_of_exists_unique (six11 h2 h.symm) with a₁ ha,
cases exists_of_exists_unique (six11 h3 h1.symm) with c₁ hc,
apply eleven3.2 ⟨a, c, a₁, c₁, (six5 h), (six5 h1), ha.1, hc.1, ha.2.symm.flip, hc.2.symm, _⟩,
exact two11 h4 (six8 ha.1 hc.1 h5) ha.2.symm.flip hc.2.symm
end

theorem eleven21d {a b c a' b' c' : point} : col a b c  → eqa a b c a' b' c' → col a' b' c' :=
begin
intros h h1,
cases six1 h,
  exact or.inl (eleven21b h_1 h1),
exact (six4.1 ((eleven21a h_1).1 h1)).1
end

end Euclidean_plane