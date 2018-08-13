import Euclid.tarski_4
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance] prop_decidable

-- Line Reflections

noncomputable def mid (a b : point) : point := classical.some (eight22 a b)

theorem ten1 (a b : point) : M a (mid a b) b := (classical.some_spec (eight22 a b)).1

@[simp] theorem mid.refl (a : point) : mid a a = a :=
begin
let h := ten1 a a,
exact (seven3.1 h).symm
end

theorem mid.symm (a b : point) : mid a b = mid b a :=
begin
let h := ten1 a b,
let h1 := ten1 b a,
exact seven17 h h1.symm
end

theorem midtoS (a b : point) : S (mid a b) a = b := (seven6 (ten1 a b)).symm

theorem midofS (a b : point) : mid b (S a b) = a := seven17 (ten1 b (S a b)) (seven5 a b)

theorem ten2 {p : point} {A : set point} : line A → p ∉ A → ∃! q, mid p q ∈ A ∧ perp A (l p q) :=
begin
intros h h_1,
rcases h with ⟨a, b, h⟩,
rw h.2 at *,
cases eight18 h_1 with x hx,
fapply exists_unique.intro,
    exact (S x p),
  split,
    suffices : mid p (S x p) = x,
      rw this,
      exact hx.1.1,
    exact seven17 (ten1 p (S x p)) (seven5 x p),
  apply (eight14f hx.1.2.symm _ _).symm,
    left,
    exact (seven5 x p).1,
  intro h_2,
  have h1 : p = x,
    exact seven10.1 h_2.symm,
  subst x,
  apply h_1,
  exact hx.1.1,
intros y hy,
have h1 : p ≠ y,
    intro h_2,
    rw ←h_2 at hy,
    rw (mid.refl p) at hy,
    exact h_1 hy.1,
let h2 := ten1 p y,
have h3 : mid p y = x,
  apply hx.2,
  split,
    exact hy.1,
  suffices : l p y = l p (mid p y),
    rw ←this,
    exact hy.2,
  apply six18 (six14 h1),
      intro h_2,
      rw ←h_2 at h2,
      apply h1,
      exact id_eqd p y p h2.2.symm,
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
let h2 := ten3a h.symm h_2,
rwa six17 a b
end

theorem ten3c {A : set point} (h : line A) {a : point} : a ∉ A → Sl h a ∉ A :=
begin
intro h1,
let h2 := ten3a h h1,
cases em (a = Sl h a),
  rwa ←h_1,
intro h3,
apply h1,
let h4 := ten1 a (Sl h a),
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
  let h1 := ten3b h h_1,
  rwa h1,
let h1 := ten3a h h_1,
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
  let h2 := ten3a h h_1,
  rw h1 at *,
  simp at h2,
  exact h2.1,
intro h1,
exact ten3b h h1
end

theorem ten9 {A : set point} (h : line A) {a : point} : a ∉ A → perp A (l a (mid a (Sl h a))) :=
begin
intro h1,
let h2 := ten3a h h1,
suffices : l a (Sl h a) = l a (mid a (Sl h a)),
  rw ←this,
  exact h2.2,
have h3 : a ≠ Sl h a,
  intro h_1,
  apply h1,
  exact (ten8 h).1 h_1.symm,
let h4 := ten1 a (Sl h a),
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
let h4 := midtoS x y,
rw h3 at h4,
let h5 := seven5 x p,
let h6 := (seven14 z).1 h5,
rw h4 at h6,
let h7 := seven6 h6,
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
    exact eight15 (ten3e h p) (ten9 h h_1),
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
    exact eight15 (ten3e h q) (ten9 h h_1),
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
let h2 := (ten10 h (Sl h a) (Sl h b)).symm.trans (h1.trans (ten10 h (Sl h c) (Sl h d))),
simpa using h2
end

theorem ten12a {a b p : point} (h : line (l a b)) : R a b p → b = mid p (Sl h p) :=
begin
intro h1,
cases em (p ∈ l a b),
    cases eight9 h1 h_1,
    subst b,
    apply false.elim,
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
  let h5 := six14 (ne.symm h_1),
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
let h5 := six14  h_2,
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
let h10 := six14 h_1,
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
      exact eight15 hx.1.1 hx.1.2,
    have h6 : xperp x' (l a' b') (l c' x'),
      suffices : perp (l a' b') (l c' x'),
        exact eight15 h3 this,
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
let h3 := hc'.1.symm.trans hc''.1,
let h4 := hc'.2.trans hc''.2.symm,
let h5 := six14 (six26 h1).1,
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

end Euclidean_plane