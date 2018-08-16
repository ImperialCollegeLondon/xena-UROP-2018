import Euclid.tarski_1
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance] prop_decidable

theorem six9 {a b p : point} : b ∈ ray p a → ray p a = ray p b :=
begin
intro h,
ext,
split,
  intro h1,
  cases h with h h2,
  cases h2 with h2 h3,
  cases h1 with h1 h4,
  cases h4 with h4 h5,
  split,
    exact h2,
  split,
    exact h4,
  cases h3,
    cases h5,
      exact five1 h.symm h3 h5,
    right,
    exact three6b h5 h3,
  cases h5,
    left,
    exact three6b h3 h5,
  exact five3 h3 h5,
intro h1,
cases h with h h2,
cases h2 with h2 h3,
cases h1 with h1 h4,
cases h4 with h4 h5,
split,
  exact h,
split,
exact h4,
cases h3,
  cases h5,
    left,
    exact three6b h3 h5,
  exact five3 h3 h5,
cases h5,
  exact five1 h2.symm h3 h5,
right,
exact three6b h5 h3
end

theorem six10 {a b c p q r : point} : sided a b c → sided p q r → eqd a b p q → eqd a c p r → cong a b c p q r :=
begin
intro h,
revert p q r,
wlog h4 : distle a b a c,
    exact (five10 a b a c),
  introv h1 h2 h3,
  repeat {split};
  try {assumption},
  have h5 : distle p q p r,
    exact five6 h4 h2 h3,  
  have h6 : B a b c,
    exact (six12 h).1 h4,
  have h7 : B p q r,
    exact (six12 h1).1 h5,
  exact (four3 h6.symm h7.symm h3.flip h2.flip).flip,
let h1 := this h.symm a_1.symm a_3 a_2,
repeat {split},
    exact h1.2.2,
  exact h1.2.1.flip,
exact h1.1
end

theorem six10a {a b c a' b' c' : point} : sided a b c → cong a b c a' b' c' → sided a' b' c' :=
begin
intro h,
revert a' b' c',
wlog h1 : B a b c := (h.2.2) using b c,
  introv h2,
  split,
    intro h_1,
    subst b',
    exact h.1.symm (id_eqd a b a' h2.1),
  split,
    intro h_1,
    subst c',
    exact h.2.1.symm (id_eqd a c a' h2.2.2),
  exact or.inl (four6 h1 h2),
apply (this h.symm _).symm,
exact ⟨a_1.2.2, a_1.2.1.flip, a_1.1⟩
end

def l (a b : point) : set point := {x | col a b x}

def line (k : set point) : Prop := ∃ a b, a ≠ b ∧ k = l a b

lemma six14 {a b : point} : a ≠ b → line (l a b) :=
begin
intro h,
existsi a,
existsi b,
split,
  exact h,
refl
end

theorem six15 {p q r : point} : p ≠ q → p ≠ r → B q p r → l p q = ray p q ∪ {p} ∪ ray p r :=
begin
intros h h1 h2,
ext,
split,
  intro h3,
  cases em (x = p),
    left, right,
    rw h_1,
    simp,
  cases h3,
    left, left,
    split,
      exact h.symm,
    split,
      exact h_1,
    left,
    exact h3,
    cases h3,
    left, left,
    split,
      exact h.symm,
    split,
      exact h_1,
    right,
    exact h3.symm,
  right,
  split,
    exact h1.symm,
  split,
    exact h_1,
  exact five2 h.symm h2 h3.symm,
intro h3,
cases h3,
  cases h3,
    cases h3 with h3 h4,
    cases h4 with h4 h5,
    cases h5,
      left,
      exact h5,
    right, left,
    exact h5.symm,
  have : x = p,
    simpa using h3,
  right, left,
  rw this,
  exact three1 q p,
cases h3 with h3 h4,
cases h4 with h4 h5,
right, right,
cases h5,
  exact (three7b h2 h5 h1).symm,
exact (three5a h2 h5).symm
end

theorem six16 {p q r : point} : p ≠ q → p ≠ r → r ∈ l p q → l p q = l p r :=
begin
intros h h1 h2,
ext,
split,
  intro h3,
  exact five4 h h2 h3,
intro h3,
have : col p r q,
  exact (four11 h2).1,
exact five4 h1 this h3
end

theorem six17 (p q : point) : l p q = l q p :=
begin
ext,
split,
  intro h1,
  exact (four11 h1).2.1,
intro h1,
exact (four11 h1).2.1
end

theorem line.symm {a b : point} (h : line (l a b)) : line (l b a) := (six17 a b) ▸ h

@[simp] theorem six17a (p q : point) : p ∈ l p q := (four11 (four12 p q)).1

@[simp] theorem six17b (p q : point) : q ∈ l p q := (four11 (four12 q p)).2.2.2.1

theorem six18 {a b : point} {L : set point} : line L → a ≠ b → a ∈ L → b ∈ L → L = l a b :=
begin
intros h h1 h2 h3,
cases h with p hp,
cases hp with q hq,
rw hq.2 at *,
cases em (a = p),
  rw h at *,
  exact six16 hq.1 h1 h3,
have ha : l p q = l p a,
  exact six16 hq.1 (ne.symm h) h2,
rw ha at *,
rw six17 p a at *,
exact six16 h h1 h3
end

theorem six18a {a p q : point} : a ∉ l p q → a ≠ p ∧ a ≠ q :=
begin
intro h,
split,
  intro h1,
  subst a,
  apply h,
  simp,
intro h1,
subst a,
simpa using h
end

theorem six19 {a b : point} : a ≠ b → ∃! L : set point, line L ∧ a ∈ L ∧ b ∈ L :=
begin
intro h,
existsi l a b,
split,
  split,
    existsi a,
    existsi b,
    split,
      exact h,
    refl,
  split;
  simp,
intros y hy,
exact six18 hy.1 h hy.2.1 hy.2.2
end

theorem six21 {a b : point} {A B : set point} : a ≠ b → line A → line B → a ∈ A → a ∈ B → b ∈ A → b ∈ B → A = B :=
begin
intros h h1 h2 h3 h4 h5 h6,
apply unique_of_exists_unique (six19 h),
  repeat {split, assumption},
  assumption,
assumption
end

def is (x : point) (A B : set point) : Prop := line A ∧ line B ∧ A ≠ B ∧ x ∈ A ∧ x ∈ B

theorem six22 {x : point} {A : set point} : line A → x ∈ A → ∃ y, x ≠ y ∧ A = l x y :=
begin
intros h h1,
let h2 := h,
cases h with u hu,
cases hu with v hv,
cases em (u = x),
  rw h at *,
  constructor,
  exact hv,
constructor,
split,
  exact ne.symm h,
have : u ∈ A,
  rw hv.2,
  simp,
exact six18 h2 (ne.symm h) h1 this
end

theorem six23 {a b c : point} : col a b c ↔ ∃ (L : set point), line L ∧ a ∈ L ∧ b ∈ L ∧ c ∈ L :=
begin
split,
  intro h,
  cases em (a = b),
    rw h_1 at *,
    cases em (b = c),
      rw h_2 at *,
      cases three14 c c with p hp,
      existsi l c p,
      split,
        exact six14 hp.2,
      simp,
    existsi l b c,
    split,
      exact six14 h_2,
    simp,
  existsi l a b,
  split,
    exact six14 h_1,
  simpa using h,
intro h,
cases h with L h,
cases em (a = b),
  rw h_1,
  exact four12 b c,
have : L = l a b,
  exact six18 h.1 h_1 h.2.1 h.2.2.1,
rw this at *,
exact h.2.2.2
end

theorem six24 : ∃ (x y z : point), ¬col x y z :=
let ⟨x, y, z, h⟩ := (two_dim point) in
begin
have : ¬col x y z,
  intro h1,
  cases h1,
    exact h.1 h1,
  cases h1,
    exact h.2.1 h1,
  exact h.2.2 h1,
exact ⟨x, ⟨y, ⟨z, this⟩⟩⟩
end

theorem six25 {a b : point} : a ≠ b → ∃ c, ¬col a b c :=
let ⟨(x : point), y, z, h⟩ := six24 in
begin
intro h1,
apply classical.by_contradiction,
rw not_exists,
intro h2,
simp at h2,
apply h,
apply six23.2,
existsi l a b,
split,
  exact six14 h1,
split,
  exact h2 x,
split,
  exact h2 y,
exact h2 z
end

lemma six13a (a : point) : ¬line (l a a) :=
begin
intro h,
cases h with p hp,
cases hp with q hq,
cases six25 hq.1 with r hr,
apply hr,
suffices : r ∈ l a a,
  rw hq.2 at this,
  exact this,
left,
exact three3 a r
end

lemma six13 {a b : point} : line (l a b) → a ≠ b := 
begin
intros h h1,
subst b,
apply six13a a,
exact h
end

def diff (a b c : point) : Prop := a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem six26 {a b c : point} : ¬col a b c → diff a b c :=
begin
intro h,
split,
  intro h,
  rw h at *,
  exact h (four12 b c),
split,
  intro h,
  rw h at *,
  exact h (four11 (four12 c a)).2.2.2.1,
intro h,
rw h at *,
exact h (four11 (four12 c b)).1
end

theorem six27 {a b c : point} {A : set point} : line A → a ∈ A → c ∈ A → B a b c → b ∈ A :=
begin
intros h h1 h2 h3,
cases em (a = c),
  rw h_1 at h3,
  have : c = b,
    exact bet_same c b h3,
  rwa this at h2,
let h4 := six18 h h_1 h1 h2,
rw h4,
right, left,
exact h3.symm
end

theorem six28 {a b c :point} : ¬col a b c → is a (l a b) (l a c) :=
begin
intro h,
split,
  exact six14 (six26 h).1,
split,
  exact six14 (six26 h).2.2,
split,
  intro h1,
  have h2 : c ∈ l a b,
    rw h1,
    simp,
  contradiction,
simp
end

-- middle points

def M (a m b : point) : Prop := B a m b ∧ eqd m a m b 

theorem M.symm {a b m : point} : M a m b → M b m a :=
begin
intro h,
split,
  exact h.1.symm,
exact h.2.symm
end

theorem seven3 {a m : point} : M a m a ↔ a = m :=
begin
split,
  intro h,
  exact bet_same a m h.1,
intro h,
rw h at *,
split,
  exact three1 m m,
exact eqd.refl m m
end

theorem seven4 (a p : point) : ∃! q, M p a q :=
begin
cases em (a = p),
  rw h,
  existsi p,
  split,
    apply seven3.2,
    refl,
  intros y hy,
  cases hy with h1 h2,
  exact id_eqd y p p h2.symm.flip,
cases seg_cons a a p p with q hq,
apply exists_unique.intro,
exact ⟨hq.1, hq.2.symm⟩,
intros y hy,
apply unique_of_exists_unique (two12 a a p p (ne.symm h)),
exact ⟨hy.1, hy.2.symm⟩,
exact hq
end

noncomputable def S (a p : point) : point := classical.some (seven4 a p)

theorem seven5 (a p : point) : M p a (S a p) := (classical.some_spec (seven4 a p)).1

theorem seven6 {a p q : point} : M p a q → q = S a p :=
begin
intro h,
exact unique_of_exists_unique (seven4 a p) h (classical.some_spec (seven4 a p)).1
end

@[simp] theorem seven7 (a p : point) : S a (S a p) = p :=
begin
cases seven5 a p with h1 h2,
generalize hq : S a p = q,
rw hq at *,
cases seven5 a q with h3 h4,
generalize hr : S a q = r,
rw hr at *,
cases em (q = a),
  rw h at *,
  have ha : a = r,
    exact id_eqd a r a h4.symm,
  rw ha at *,
  exact id_eqd r p r h2,
apply unique_of_exists_unique (two12 a a p q h),
  split,
    exact h3,
  exact (eqd.trans h2 h4).symm,
split,
  exact h1.symm,
exact eqd.refl a p
end

theorem seven8 (a p : point) : ∃! q, S a q = p :=
begin
existsi S a p,
split,
  exact seven7 a p,
intros q h,
rw ←h,
exact (seven7 a q).symm
end

theorem seven9 {a p q : point} : S a p = S a q → p = q :=
begin
intro h,
let p' := S a p,
apply unique_of_exists_unique (seven8 a p'),
  simp,
rw ←h
end

theorem seven9a {a b : point} (p : point) : a ≠ b → S p a ≠ S p b :=
begin
intros h h1,
exact h (seven9 h1)
end

theorem seven10 {a p : point} : S a p = p ↔ p = a :=
begin
split,
  intro h,
  have : M p a (S a p),
    exact seven5 a p,
  rw h at *,
  exact seven3.1 this,
intro h,
rw h,
have : M a a (S a a),
  exact seven5 a a,
cases this with h1 h2,
exact id_eqd (S a a) a a h2.symm.flip
end

@[simp] theorem seven11 (a : point) : S a a = a :=
begin
apply seven10.2,
refl
end

theorem seven12 {a p : point} : a ≠ p → a ≠ S a p :=
begin
intros h h1,
apply h,
have h2 : S a a = a,
  exact seven11 a,
exact seven9 (eq.trans h2 h1)
end

theorem seven13 (a p q : point) : eqd p q (S a p) (S a q) :=
begin
have hp : M p a (S a p),
  exact seven5 a p,
have hq : M q a (S a q),
  exact seven5 a q,
generalize hp' : S a p = p',
generalize hq' : S a q = q',
rw hp' at *,
rw hq' at *,
cases em (p = a),
  have : S a p = p,
    exact seven10.2 h,
  rw h at *,
  rw this at *,
  rw ←hp' at *,
  exact hq.2,
cases seg_cons p q a p' with x hx,
cases seg_cons p' q a x with x' hx',
cases seg_cons q p a q' with y hy,
cases seg_cons q' p a y with y' hy',
have h1 : B a p x,
  exact three6a hp.1.symm hx.1,
have h2 : B p p' x',
  exact three6a hx.1.symm hx'.1,
have h3 : B a p' x',
  exact three6a hp.1 h2,
have h4 : B a q y,
  exact three6a hq.1.symm hy.1,
have h5 : B q q' y',
  exact three6a hy.1.symm hy'.1,
have h6 : B a q' y',
  exact three6a hq.1 h5,
have h7 : eqd a x y a,
  exact two11 h1 h4.symm hy.2.symm.flip hx.2,
have h8 : eqd a x a x',
  exact two11 h1 h3 hp.2 (eqd.trans hx.2 hx'.2.symm),
have h9 : eqd a x y' a,
  exact two11 h1 h6.symm hy'.2.symm.flip (eqd.trans hx.2 hq.2.flip),
have h10 : B x a p',
      exact three5b hx.1.symm hp.1,
have h11 : B y a q',
      exact three5b hy.1.symm hq.1,
have h12 : afs x a x' y' y' a y x,
  repeat {split},
    exact three6b h10 hx'.1,
    exact (three6b h11 hy'.1).symm,
    exact two4 h9,
    exact two5 (eqd.trans h8.symm h7),
    exact two5 (eqd.refl x y'),
  exact two4 h9.symm,
have h13 : x ≠ a,
  intro h_1,
  rw h_1 at h1,
  exact h (bet_same a p h1).symm,
have h14 : eqd x' y' y x,
  exact afive_seg h12 h13,
have h15 : ifs y q a x y' q' a x',
  repeat {split},
    exact h4.symm,
    exact h6.symm,
    exact eqd.trans h7.symm h9,
    exact hq.2.flip,
    exact two5 h14.symm,
  exact h8,
let h16 := four2 h15,
have h17 : ifs x p a q x' p' a q',
  repeat {split},
    exact h1.symm,
    exact h3.symm,
    exact h8.flip,
    exact hp.2.flip,
    exact h16.flip,
  exact hq.2,
exact four2 h17
end

theorem seven15 (a : point) {p q r : point} : B p q r ↔ B (S a p) (S a q) (S a r) :=
begin
split,
  intro h,
  apply four6 h,
  repeat {split};
  exact seven13 a _ _, 
intro h,
rw ←(seven7 a p),
rw ←(seven7 a q),
rw ←(seven7 a r),
apply four6 h,
repeat {split};
exact seven13 a _ _, 
end

theorem seven16 (a : point) {p q r s : point}: eqd p q r s ↔ eqd (S a p) (S a q) (S a r) (S a s) :=
begin
split,
  intro h,
  exact (seven13 a p q).symm.trans (h.trans (seven13 a r s)),
intro h,
let h1 := eqd.trans (seven13 a (S a p) (S a q)).symm (eqd.trans h (seven13 a (S a r) (S a s))),
simpa using h1
end

theorem seven16a (a : point) {p q r : point} : cong p q r (S a p) (S a q) (S a r) :=
begin
repeat {split};
exact seven13 a _ _
end

theorem seven14 (a : point) {p q r : point} : M p q r ↔ M (S a p) (S a q) (S a r) :=
begin
split,
  intro h,
  cases h with h h1,
  split,
    exact (seven15 a).1 h,
  exact (seven16 a).1 h1,
intro h,
cases h with h h1,
split,
  exact (seven15 a).2 h,
exact (seven16 a).2 h1
end

theorem seven17 {a b p q : point} : M p a q → M p b q → a = b :=
begin
intros h h1,
let h2 := seven6 h,
let h3 := seven13 a q b,
let h4 := seven7 a p,
rwa ←h2 at h4,
rw h4 at h3,
have h6 : eqd p b p (S a b),
  exact eqd.trans h1.2.flip h3,
let h7 := seven13 a p b,
rw ←h2 at h7,
have h8 : eqd q b q (S a b),
  exact eqd.trans h1.2.symm.flip h7,
have h9 : b = (S a b),
  exact four19 h1.1 h6 h8.flip,
exact (seven10.1 h9.symm).symm
end

theorem seven18 {a b p : point} : S a p = S b p → a = b :=
begin
intro h,
generalize h1 : S a p = q,
let h2 := seven5 a p,
rw h1 at h2,
let h3 := seven5 b p,
rw (eq.trans h.symm h1) at h3,
exact seven17 h2 h3
end

theorem seven19 {a b p : point} : S a (S b p) = S b (S a p) ↔ a = b :=
begin
split,
  intro h,
  generalize h1 : S a p = q,
  let h2 := seven5 a p,
  rw h1 at *,
  let h3 := seven5 a (S b p),
  rw h at h3,
  cases h3 with h3 h4,
  let h5 := (seven15 b).1 h3,
  let h6 := (seven16 b).1 h4,
  rw seven7 b p at *,
  rw seven7 b q at *,
  have h7 : M p (S b a) q,
    split;
    assumption,
  have h8 : a = (S b a),
    exact seven17 h2 h7,
  exact seven10.1 h8.symm,
intro h,
rw h
end

theorem seven20 {a m b : point} : col a m b → eqd m a m b → a = b ∨ M a m b :=
begin
intros h h1,
cases h,
  right,
  split;
  assumption,
cases h,
  left,
  let h2 := three3 b m,
  have h3 : eqd a b b b,
    exact four3 h.symm h2 h1.flip (eqd.refl b m),
  exact id_eqd a b b h3,
left,
let h2 := three3 a m,
have h3 : eqd b a a a,
  exact four3 h h2 h1.symm.flip (eqd.refl a m),
exact id_eqd a b a h3.flip
end

theorem seven21 {a b c d p : point} : ¬col a b c → b ≠ d → eqd a b c d → eqd b c d a → 
col a p c → col b p d → M a p c ∧ M b p d :=
begin
intros h h1 h2 h3 h4 h5,
cases four14 (four11 h5).1 (two5 (eqd.refl b d)) with q hq,
let h6 := four13 (four11 h5).1 hq,
have h7 : fs b d p a d b q c,
  split,
    exact (four11 h5).1,
  split,
    exact hq,
  split,
    exact h2.flip,
  exact h3.symm,
have h8 : fs b d p c d b q a,
  split,
    exact (four11 h5).1,
  split,
    exact hq,
  split,
    exact h3,
  exact h2.symm.flip,
let h9 := four16 h7 h1,
let h10 := four16 h8 h1,
  have h11 : cong a p c c q a,
  split,
    exact h9.flip,
  split,
    exact h10,
  exact two5 (eqd.refl a c),
let h12 := four13 h4 h11,
have h13 : p ∈ l a c,
  exact (four11 h4).1,
have h14 : p ∈ l b d,
  exact (four11 h5).1,
have h15 : q ∈ l a c,
  exact (four11 h12).2.2.2.1,
have h16 : q ∈ l b d,
  exact (four11 h6).2.1,
have h17 : p = q,
  by_contradiction h_1,
  have h_2 : l a c = l b d,
    exact six21 h_1 (six14 (six26 h).2.2) (six14 h1) h13 h14 h15 h16,
  apply h,
  suffices : b ∈ l a c,
    exact (four11 this).1,
  rw h_2,
  simp,
rw h17 at *,
split,
  cases seven20 h4 h9,
    exfalso,
    exact ((six26 h).2.2 h_1),
  assumption,
cases seven20 h5 (hq.2.2).flip,
  contradiction,
assumption
end

def hourglass (a b c p q m n : point) : Prop := B a c p ∧ B b c q ∧ eqd c a c b ∧ eqd c p c q ∧ 
M a m b ∧ M p n q

lemma seven23 {a b c p q m n : point} : hourglass a b c p q m n → distle c a c q → B m c n :=
begin
intros h h_1,
cases h with h h1,
cases h1 with h1 h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
cases h4 with h4 h5,
cases em (p = c),
  rw h_2 at *,
  have h_3 : q = c,
    exact id_eqd q c c h3.symm.flip,
  rw h_3 at *,
  have h_4 : c = n,
    exact seven3.1 h5,
  rw h_4 at *,
  exact three1 m n,
generalize h6 : S c p = a',
generalize h7 : S c q = b',
generalize h8 : S c n = m',
have h9 : M a' m' b',
  let h_3 := (seven14 c).1 h5,
  rwa [h6, h7, h8] at h_3,
have h10 : M p c a',
  let h10 := seven5 c p,
  rwa h6 at h10,
have h11 : M q c b',
  let h11 := seven5 c q,
  rwa h7 at h11,
have h12 : M n c m',
  let h12 := seven5 c n,
  rwa h8 at h12,
have h13 : distle c a c a',
  exact five6 h_1 (eqd.refl c a) (eqd.trans h3.symm h10.2),
cases em (a = c),
  rw h_3 at *,
  have : b = c,
    exact id_eqd b c c h2.symm.flip,
  rw this at *,
  have : c = m,
    exact seven3.1 h4,
  rw this,
  exact three3 m n,
have h_4 : a' ≠ c,
  intro h_4,
  rw h_4 at *,
  have : eqd c a c c,
    exact five9 h13 (five11 c c a),
  exact h_3 (id_eqd a c c this.flip),
have h14 : sided c a a',
  apply six3.2,
  split,
    exact h_3,
  split,
    exact h_4,
  existsi p,
  split,
    exact h_2,
  split,
    exact h,
  exact h10.1.symm,
have h15 : B c a a',
  exact (six12 h14).1 h13,
have h16 : distle c b c b',
  exact five6 h_1 h2 h11.2,
have h_5 : q ≠ c,
  intro h_5,
  rw h_5 at *,
  exact h_2 (id_eqd p c c h3.flip),
cases em (b = c),
  rw h_6 at *,
  have : a = c,
   exact id_eqd a c c h2.flip,
  rw this at *,
  have : c = m,
    exact seven3.1 h4,
  rw this,
  exact three3 m n,
have h_7 : b' ≠ c,
  intro h_7,
  rw h_7 at *,
  have : eqd c b c c,
    exact five9 h16 (five11 c c b),
  exact h_6 (id_eqd b c c this.flip),
have h17 : sided c b b',
  apply six3.2,
  split,
    exact h_6,
  split,
    exact h_7,
  existsi q,
  split,
    exact h_5,
  split,
    exact h1,
  exact h11.1.symm,
have h18 : B c b b',
  exact (six12 h17).1 h16,
cases three17 h15.symm h18.symm h9.1 with r hr,
have h19 : B r c n,
  exact three6a hr.1 h12.1.symm,
suffices : r = m,
  rwa this at h19,
have h20 : ifs a' a c m' b' b c m',
  repeat {split},
    exact h15.symm,
    exact h18.symm,
    exact eqd.trans h10.2.symm.flip (eqd.trans h3.flip h11.2.flip),
    exact h2.flip,
    exact h9.2.flip,
  exact eqd.refl c m',
let h20 := four2 h20,
have h21 : col m' c r,
  right, left,
  exact hr.1.symm,
have h22 : eqd r a r b,
  cases em (m' = c),
    rw h_8 at *,
    have : c = r,
      exact bet_same c r hr.1,
    rw this at *,
    exact h20.flip,
  exact four17 h_8 h21 h20.flip h2,
have h23 : M a r b,
  split,
    exact hr.2,
  exact h22,
exact seven17 h23 h4
end

theorem seven22 {a b c p q m n : point} : hourglass a b c p q m n → B m c n :=
begin
intro h,
cases five10 c a c q,
  exact seven23 h h_1,
cases h with h h1,
cases h1 with h1 h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
cases h4 with h4 h5,
have h6 : hourglass q p c b a n m,
  repeat {split},
    exact h1.symm,
    exact h.symm,
    exact h3.symm,
    exact h2.symm,
    exact h5.1.symm,
    exact h5.2.symm,
    exact h4.1.symm,
  exact h4.2.symm,
exact (seven23 h6 h_1).symm
end

theorem seven24 {a p : point} {A : set point} : line A → a ∈ A → (p ∈ A ↔ (S a p) ∈ A) :=
begin
intros h h1,
split,
  intro h2,
  cases em (a = p),
    let h3 := seven10.2 h_1.symm,
    rwa h3,
  let h3 := six18 h h_1 h1 h2,
  rw h3,
  let h4 := seven5 a p,
  right, right,
  exact h4.1.symm,
intro h2,
cases em (a = (S a p)),
  let h3 := seven10.2 h_1.symm,
  rw ←seven7 a p,
  rwa h3,
let h3 := six18 h h_1 h1 h2,
rw h3,
let h4 := seven5 a p,
right, right,
exact h4.1
end

theorem seven25 {a b c : point} : eqd c a c b → ∃ x, M a x b :=
begin
intro h,
cases em (col a c b),
  cases seven20 h_1 h,
    rw h_2 at *,
    existsi b,
    split,
      exact three1 b b,
    exact eqd.refl b b,
  constructor, exact h_2,
cases three14 c a with p hp,
cases seg_cons b a p c with q hq,
cases pasch p q c a b hp.1.symm hq.1.symm with r hr,
cases pasch c b p a r hp.1 hr.2 with x hx,
existsi x,
suffices : eqd x a x b,
  split,
    exact hx.1,
  exact this,
suffices : eqd r a r b,
  have h1 : col c r x,
    right, left,
    exact hx.2,
  cases em (c = r),
    rw h_2 at hx,
    have : r = x,
      exact bet_same r x hx.2,
    rw this at *,
    exact this,
  exact four17 h_2 h1 h this,
have h1 : afs c a p b c b q a,
  repeat {split},
    exact hp.1,
    exact hq.1,
    exact h,
    exact hq.2.symm,
    exact h.symm,
  exact two5 (eqd.refl a b),
have h2 : eqd p b q a,
  exact afive_seg h1 (six26 h_1).1.symm,
cases four5 hr.2 h2.flip with r' hr',
have h3 : ifs b r p a a r' q b,
  repeat {split},
    exact hr.2,
    exact hr'.1,
    exact hr'.2.2.2,
    exact hr'.2.2.1,
    exact two4 (eqd.refl a b),
  exact hq.2.symm.flip,
have h4 : ifs b r p q a r' q p,
  repeat {split},
    exact hr.2,
    exact hr'.1,
    exact hr'.2.2.2,
    exact hr'.2.2.1,
    exact hq.2,
  exact two5 (eqd.refl p q),
let h5 := four2 h3,
let h6 := four2 h4,
have h7 : cong a r q b r' p,
  split,
    exact h5.flip,
  split,
    exact h6,
  exact h2.symm.flip,
have h8 : col a r q,
  left, exact hr.1,
let h9 := four13 h8 h7,
have h_2 : a ≠ q,
  intro h_2,
  rw ←h_2 at *,
  have : col a c b,
    right, left,
    exact hq.1,
  exact h_1 this,
have h_3 : b ≠ p,
  intro h_3,
  rw ←h_3 at *,
  have : col a c b,
    right, right,
    exact hp.1.symm,
  exact h_1 this,
have h10 : l a q ≠ l b p,
  intro h_4,
  suffices : a ∈ l b p,
    have h_6 : col a p c,
      right, right,
      exact hp.1,
    exact h_1 (five4 hp.2 h_6 (four11 this).2.2.2.2),
  rw ←h_4,
  simp,
have h11 : col b p r,
  right, left,
  exact hr.2.symm,
  have h12 : col a q r',
    right, left,
    exact hr'.1.symm,
have : r = r',
  by_contradiction h_4,
  exact h10 (six21 h_4 (six14 h_2) (six14 h_3) (four11 h8).1 h11 h12 (four11 h9).1),
rw this at *,
exact h5
end

end Euclidean_plane
