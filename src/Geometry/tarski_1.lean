import geometry.axioms data.set tactic.interactive
open classical
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance, priority 0] prop_decidable

--Conclusions from the first 5 axioms
@[simp] theorem eqd.refl (a b : point) : eqd a b a b :=
eqd_trans (eqd_refl b a) (eqd_refl b a)

theorem eqd.symm {a b c d : point} : eqd a b c d → eqd c d a b :=
λ h, eqd_trans h (eqd.refl a b)

theorem eqd.trans {a b c d e f: point} : eqd a b c d → eqd c d e f → eqd a b e f :=
assume h h1,
eqd_trans h.symm h1

theorem two4 {a b c d : point} : eqd a b c d → eqd b a c d := eqd_trans (eqd_refl a b)

theorem two5 {a b c d : point} : eqd a b c d → eqd a b d c := assume h, eqd.trans h (eqd_refl c d)

theorem eqd.flip {a b c d : point} : eqd a b c d → eqd b a d c := assume h, two4 (two5 h)

theorem two7 {a b c d : point} : eqd a b c d → a ≠ b → c ≠ d :=
begin
intros h h1 h2,
subst d,
exact h1 (id_eqd h)
end

@[simp] theorem two8 (a b : point) : eqd a a b b := 
let ⟨x, h⟩ := seg_cons a b b b in
have a = x := id_eqd h.2,
by rw ←this at h; exact h.2

def afs (a b c d a' b' c' d' : point) : Prop := B a b c ∧ B a' b' c' ∧ eqd a b a' b' 
∧ eqd b c b' c' ∧ eqd a d a' d' ∧ eqd b d b' d'

theorem afive_seg {a b c d a' b' c' d' : point} : afs a b c d a' b' c' d' → 
a ≠ b → eqd c d c' d' := 
λ h h1, five_seg h1 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem two11 {a b c a' b' c' : point} : B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a c a' c' := 
begin
intros h h1 h2 h3,
by_cases h_1 : a = b,
  subst b,
  rwa id_eqd h2.symm,
exact (five_seg h_1 h h1 h2 h3 (two8 a a') h2.flip).flip
end

theorem two12 {a q x y b c : point} (h : q ≠ a) : B q a x → eqd a x b c → B q a y → eqd a y b c → x = y :=
begin
intros h1 h2 h3 h4,
by_contradiction h_1,
suffices : eqd x x x y,
  exact h_1 (id_eqd this.symm),
apply five_seg h h1 h1 _ _ (two11 h1 h3 _ (h2.trans h4.symm)) (eqd.trans h2 h4.symm);
simp
end

-- Properties of B

@[simp] theorem three1 (a b : point) : B a b b := 
let ⟨x, h, h1⟩ := seg_cons b b b a in
by rwa (id_eqd h1).symm at h

theorem B.symm {a b c : point} : B a b c → B c b a :=
λ h, let ⟨x, h1, h2⟩ := pasch h (three1 b c) in
by rwa (bet_same h1).symm at h2

theorem three2 (a b c : point) : B a b c ↔ B c b a :=
⟨B.symm, B.symm⟩

@[simp] theorem three3 (a b : point) : B a a b := 
(three1 b a).symm

instance dec_eqp : decidable_eq point :=
begin
intros a b,
cases dec_B a b a,
  left,
  intro h_1,
  subst b,
  exact h (three1 a a),
right,
exact bet_same h
end

theorem three4 {a b c: point} : B a b c → B b a c → a = b :=
λ h h1, let ⟨x, hx⟩ := pasch h h1 in
(bet_same hx.2).trans (bet_same hx.1).symm

theorem three5a {a b c d : point} : B a b d → B b c d → B a b c :=
λ h h1, let ⟨x, h2, h3⟩ := pasch h h1 in
(bet_same h2).symm ▸ h3.symm

theorem three6a {a b c d : point} : B a b c → B a c d → B b c d :=
λ h h1, (three5a h1.symm h.symm).symm

theorem three7a {a b c d : point} : B a b c → B b c d → b ≠ c → B a c d :=
λ h h1 h2, let ⟨x, h3, h4⟩ := seg_cons c c d a in
(two12 h2 (three6a h h3) h4 h1 (eqd.refl c d)) ▸ h3

theorem three5b {a b c d : point} : B a b d → B b c d → B a c d :=
begin
intros h h1,
cases em (b = c),
  rwa h_1 at h,
exact three7a (three5a h h1) h1 h_1
end

theorem three6b {a b c d : point} : B a b c → B a c d → B a b d :=
λ h h1, (three5b h1.symm h.symm).symm

theorem three7b {a b c d : point} : B a b c → B b c d → b ≠ c → B a b d :=
λ h h1 h2, (three5b (three7a h h1 h2).symm h.symm).symm

theorem three13 : (P1 : point) ≠ P2 := 
begin
intro h,
apply (two_dim point).1,
rw h,
exact three3 P2 P3
end

def three14 (a b : point) : {c // B a b c ∧ b ≠ c} := 
begin
cases seg_cons b P1 P2 a with c h,
cases h with h1 h2,
refine ⟨c, h1, _⟩,
intro h_1,
subst c,
exact three13 (id_eqd h2.symm)
end

theorem three15 {a b c : point} : B a b c → eqd a b a c → b = c :=
begin
intros h h1,
by_cases h_1 : a = c,
  subst c,
  exact id_eqd h1.flip,
cases three14 c a with d hd,
exact two12 hd.2.symm (three5a hd.1.symm h) h1 hd.1.symm (eqd.refl a c)
end

theorem three17 {a b c a' b' p : point} : B a b c → B a' b' c 
→ B a p a' → {q // B p q c ∧ B b q b'} :=
begin
intros h1 h2 h3,
cases pasch h3 h2.symm with x h4,
cases pasch h1.symm h4.2 with y h5,
exact ⟨y, three5b h4.1 h5.2, h5.1⟩
end

-- cong + col

def ifs (a b c d a' b' c' d' : point) : Prop := B a b c ∧ B a' b' c' ∧ eqd a c a' c' 
∧ eqd b c b' c' ∧ eqd a d a' d' ∧ eqd c d c' d'

theorem four2 {a b c d a' b' c' d' : point} : ifs a b c d a' b' c' d' → eqd b d b' d' :=
begin
rintro ⟨h, h1, h2, h3, h4, h5⟩,
cases em (a = c),
  subst c,
  rw (bet_same h) at h3 h5,
  rwa (id_eqd h3.symm).symm at h5,
cases three14 a c with e he,
cases seg_cons c' c e a' with e' he',
have : afs a c e d a' c' e' d',
  repeat {split};
    try{assumption},
    exact he.1,
    exact he'.1,
  exact he'.2.symm,
have : eqd e d e' d',
  exact afive_seg this h_1,
exact five_seg he.2.symm (three6a h he.1).symm (three6a h1 he'.1).symm he'.2.symm.flip h3.flip this h5
end

theorem four3 {a b c a' b' c' : point} : B a b c → B a' b' c' → eqd a c a' c' 
→ eqd b c b' c' → eqd a b a' b' :=
begin
intros h h1 h2 h3,
  have : ifs a b c a a' b' c' a',
  repeat {split};
    try{assumption},
    exact two8 a a',
  exact h2.flip,
exact (four2 this).flip
end

def cong (a b c a' b' c' : point) : Prop := eqd a b a' b' ∧ eqd b c b' c' ∧ eqd a c a' c'

@[simp] theorem cong.refl (a b c : point) : cong a b c a b c :=
begin
repeat {split};
exact eqd.refl _ _
end

theorem cong.symm {a b c a' b' c' : point} : cong a b c a' b' c' → cong a' b' c' a b c :=
begin
intro h,
split,
  exact h.1.symm,
split,
  exact h.2.1.symm,
exact h.2.2.symm
end

theorem cong.trans {a b c a' b' c' a'' b'' c'' : point} : cong a b c a' b' c' → cong a' b' c' a'' b'' c'' → cong a b c a'' b'' c'' :=
begin
intros h h1,
split,
  exact eqd.trans h.1 h1.1,
split,
  exact eqd.trans h.2.1 h1.2.1,
exact eqd.trans h.2.2 h1.2.2
end

lemma four4 {a b c a' b' c' : point} : cong a b c a' b' c' → cong a c b a' c' b' ∧ cong b a c b' a' c' ∧ 
cong b c a b' c' a' ∧ cong c a b c' a' b' ∧ cong c b a c' b' a' :=
λ h, ⟨⟨h.2.2, h.2.1.flip, h.1⟩, ⟨h.1.flip, h.2.2, h.2.1⟩, ⟨h.2.1, h.2.2.flip, h.1.flip⟩, 
⟨h.2.2.flip, h.1, h.2.1.flip⟩, ⟨h.2.1.flip, h.1.flip, h.2.2.flip⟩⟩

def four5 {a b c a' c' : point} : B a b c → eqd a c a' c' 
→ {b'// B a' b' c' ∧ cong a b c a' b' c'} :=
begin
intros h h1,
cases three14 c' a' with d' hd,
cases seg_cons a' a b d' with b' hb,
cases seg_cons b' b c d' with c'' hc,
have h2 : B a' b' c'' ∧ B d' a' c'',
  split,
    exact three6a hb.1 hc.1,
  exact three6b hb.1 hc.1,
have h3 : eqd a' c'' a c,
  exact two11 h2.1 h hb.2 hc.2,
have h4 : c' = c'',
  exact (two12 hd.2.symm) hd.1.symm h1.symm h2.2 h3,
rw ←h4 at *,
existsi b',
split,
  exact h2.1,
unfold cong,
split,
  apply four3 h h2.1,
    exact h3.symm,
  exact hc.2.symm,
split,
  exact hc.2.symm,
exact h3.symm
end

theorem four6 {a b c a' b' c' : point} : B a b c → cong a b c a' b' c' → B a' b' c' :=
begin
intros h h1,
cases h1 with h1 h2,
cases h2 with h2 h3,
cases four5 h h3 with b'' hb,
cases hb with hb hb1,
cases hb1 with hb1 hb2,
cases hb2 with hb2 hb3,
have : ifs a' b'' c' b'' a' b'' c' b',
  repeat {split};
    try {assumption},
    exact eqd.trans hb3.symm h3,
    exact eqd.refl _ _,
    exact eqd.trans hb1.symm h1,
    have : eqd b'' c' b' c',
      exact eqd.trans hb2.symm h2,
    exact this.flip,
have : b'' = b',
  have h4 : eqd b'' b'' b'' b',
    exact four2 this,
  exact id_eqd h4.symm,
rwa this at *
end

def col (a b c : point) : Prop := B a b c ∨ B b c a ∨ B c a b

instance dec_col : ∀ (a : point) b c, decidable (col a b c) :=
begin
intros,
cases dec_B a b c,
  cases dec_B b c a,
    cases dec_B c a b,
      left,
      unfold col,
      simp *,
    exact is_true (or.inr (or.inr h_2)),
  exact is_true (or.inr (or.inl h_1)),
exact is_true (or.inl h)
end

theorem four11 {a b c : point} : col a b c → col a c b ∧ col b a c ∧ col b c a ∧ col c a b ∧ col c b a := 
begin
intro h,
cases h with h1 h2,
  have := h1.symm,
  repeat {split}; unfold col;
  simp *,
cases h2 with h2 h3,
  have := h2.symm,
  repeat {split};unfold col;
  simp *,
have := h3.symm,
repeat {split}; unfold col;
simp *
end

theorem four10 {a b c : point} : ¬col a b c → ¬col a c b ∧ ¬col b a c ∧ ¬col b c a ∧ ¬col c a b ∧ ¬col c b a :=
begin
intro h,
split,
  intro h_1,
  exact h (four11 h_1).1,
split,
  intro h_1,
  exact h (four11 h_1).2.1,
split,
  intro h_1,
  exact h (four11 h_1).2.2.2.1,
split,
  intro h_1,
  exact h (four11 h_1).2.2.1,
intro h_1,
exact h (four11 h_1).2.2.2.2
end

theorem four12 (a b : point) : col a a b := 
or.inl (three3 a b)

theorem four13 {a b c a' b' c' : point} : col a b c → cong a b c a' b' c' → col a' b' c' :=
begin
intros h h1,
unfold col,
cases h,
  have := four6 h h1,
  simp *,
cases h,
  have := four6 h (four4 h1).2.2.1,
  simp *,
have := four6 h (four4 h1).2.2.2.1,
simp *
end

def four14 {a b c a' b' : point} (h : col a b c) (h1 : eqd a b a' b') : {c' // cong a b c a' b' c'} :=
begin
cases dec_B a b c,
  cases dec_B b c a,
    replace h : B c a b,
      unfold col at h,
      simpa [h_1, h_2] using h,
      cases seg_cons a' a c b' with c' hc,
    exact ⟨c', h1, two11 h.symm hc.1 h1.flip hc.2.symm, hc.2.symm⟩,
  cases four5 h_2 h1.flip with c' hc,
  exact ⟨c', (four4 hc.2).2.2.2.1⟩,
cases seg_cons b' b c a' with c' hc,
exact ⟨c', h1, hc.2.symm, two11 h_1 hc.1 h1 hc.2.symm⟩
end

def fs (a b c d a' b' c' d' : point) : Prop := col a b c ∧ cong a b c a' b' c' ∧
eqd a d a' d' ∧ eqd b d b' d'

theorem four16 {a b c d a' b' c' d' : point} : fs a b c d a' b' c' d' → a ≠ b → eqd c d c' d' :=
begin
intros h1 h,
cases h1 with h1 h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
cases h1 with ha hbc,
  exact five_seg h ha (four6 ha h2) h2.1 h2.2.1 h3 h4,
cases hbc with hb hc,
  have : ifs b c a d b' c' a' d',
    repeat {split};
      try {assumption},
        exact four6 hb (four4 h2).2.2.1,
      exact h2.1.flip,
    exact h2.2.2.flip,
  exact four2 this,
rw three2 at hc,
have : cong b a c b' a' c',
  unfold cong,
  split,
    exact h2.1.flip,
  split,
    exact h2.2.2,
  exact h2.2.1,
exact five_seg h.symm hc (four6 hc this) h2.1.flip h2.2.2 h4 h3
end

theorem four17 {a b c p q : point} : a ≠ b → col a b c → eqd a p a q → eqd b p b q → eqd c p c q :=
begin
intros h h1 h2 h3,
have : fs a b c p a b c q,
  unfold fs,
  repeat {split}; try {assumption};
  exact eqd.refl _ _,
exact four16 this h
end

theorem four18 {a b c c' : point} : a ≠ b → col a b c → eqd a c a c' → eqd b c b c' → c = c':=
begin
intros h h3 h1 h2,
have : eqd c c c c',
  exact four17 h h3 h1 h2,
exact id_eqd this.symm
end

theorem four19 {a b c b' : point} : B a b c → eqd a b a b' → eqd b c b' c → b = b' :=
begin
intros h h1 h2,
cases em (a = c) with h3 h4,
  rw ←h3 at *,
  have : a = b, exact bet_same h,
  rw this at *,
  exact id_eqd h1.symm,
have : col a c b,
  right, left,
  exact h.symm,
exact four18 h4 this h1 h2.flip
end

-- Ordering collinear points & Comparing distances

theorem five1 {a b c d : point} : a ≠ b → B a b c → B a b d → B a c d ∨ B a d c :=
begin
intros h h1 h2,
cases em (c = d),
  left, rw h_1 at *, exact three1 a d,
cases seg_cons d d c a with c' hc,
cases seg_cons c c d a with d' hd,
cases seg_cons c' c b d with b' ha,
cases seg_cons d' d b c with b'' hb,
have h_2 : d ≠ c',
  intro h_2,
  rw ←h_2 at hc,
  have : c = d,
    exact id_eqd hc.2.symm.flip,
  contradiction,
have h_3 : d' ≠ c,
  intro h_3,
  rw h_3 at hd,
  have : c = d,
    exact id_eqd hd.2.symm,
  contradiction,
have h3 : B b d c',
  exact three6a h2 hc.1,
have h4 : eqd b c' b'' c,
  exact two11 h3 hb.1.symm hb.2.symm.flip (eqd.trans hc.2 hd.2.symm.flip),
have h5 : B b c' b',
  exact three7a h3 ha.1 h_2,
have h_4 : B b c d',
  exact three6a h1 hd.1,
have h6 : B b'' c b,
  exact three7a hb.1.symm h_4.symm h_3,
have h7 : eqd b b' b'' b,
  exact two11 h5 h6 h4 ha.2,
have h_5 : B a b b',
  have : B a d b',
    exact three7b hc.1 ha.1 h_2,
  exact three6b h2 this,
have h_6 : B a b b'',
  have : B a c b'',
    exact three7b hd.1 hb.1 h_3.symm,
  exact three6b h1 this,
have h8 : b' = b'',
  apply two12 h h_5 (eqd.refl b b') h_6,
  exact two4 h7.symm,
rw ←h8 at *,
have h9 : afs b c d' c' b' c' d c,
  repeat {split}; try {assumption},
    exact ha.1.symm,
    exact ha.2.symm.flip,
    exact eqd.trans hd.2 hc.2.symm.flip,
  exact two5 (eqd.refl c c'),
cases em (b = c),
  left,
  rw ←h_7, exact h2,
have h10 : eqd c d c' d',
  exact (afive_seg h9 h_7).symm.flip,
cases pasch hd.1.symm hc.1.symm with e he,
have h11 : ifs d e d' c d e d' c',
  repeat {split}; try {assumption},
    exact he.2,
    exact he.2,
    exact eqd.refl d d',
    exact eqd.refl e d',
    exact hc.2.symm,
  exact eqd.trans hd.2.flip h10.flip,
have h12 : ifs c e c' d c e c' d',
  repeat {split}; try {assumption},
    exact he.1,
    exact he.1,
    exact eqd.refl c c',
    exact eqd.refl e c',
    exact hd.2.symm,
  exact eqd.trans hc.2.flip h10,
have h_8 : eqd e c e c',
  exact four2 h11,
have h_9 : eqd e d e d',
  exact four2 h12,
cases em (c = c'),
  rw ←h_10 at hc,
  right, exact hc.1,
cases seg_cons c c d' c' with p hp,
cases seg_cons c c e d' with r hr,
cases seg_cons r r p p with q hq,
have h13 : afs d' c r p p c e d',
  repeat {split},
    exact hr.1,
    exact three5a hp.1.symm he.1,
    exact hp.2.symm.flip,
    exact hr.2,
    exact two4 (eqd.refl p d'),
  exact hp.2,
have h_11 : eqd r p e d',
  exact afive_seg h13 h_3,
have h_12 : eqd r q e d,
  exact eqd.trans hq.2 (eqd.trans h_11 h_9.symm),
have h14 : afs d' e d c p r q c,
  repeat {split},
    exact he.2.symm,
    exact hq.1,
    exact h_11.symm.flip,
    exact h_12.symm,
    exact hp.2.symm.flip,
  exact hr.2.symm.flip,
have h_13 : eqd d' d p q,
  exact two11 he.2.symm hq.1 h_11.symm.flip h_12.symm,
cases em (d' = e),
  rw ←h_14 at *,
  have : d' = d,
    exact id_eqd h_9,
  rw this at *,
  left, exact hd.1,
have h_15 : eqd c q c d,
  exact (afive_seg h14 h_14).symm.flip,
have h15 : eqd c p c q,
  exact eqd.trans hp.2 (eqd.trans hd.2 h_15.symm),
have h_16 : r ≠ c,
  intro hrc,
  rw hrc at *,
  have : c = e,
    exact id_eqd hr.2.symm,
  rw ←this at *,
  have : c = c',
    exact id_eqd h_8.symm,
  exact h_10 this,
have h16 : col r c d',
  left, exact hr.1.symm,
have h_17 : eqd d' p d' q,
  exact four17 h_16 h16 hq.2.symm h15,
have h17 : col c d' b,
  right, right, exact h_4,
have h18 : col c d' b',
  left, exact hb.1,
have h_18 : eqd b p b q,
  exact four17 h_3.symm h17 h15 h_17,
have h_19 : eqd b' p b' q,
  exact four17 h_3.symm h18 h15 h_17,
have h19 : col b b' c',
  right, left, exact h5.symm,
have h_20 : b ≠ b',
  intro hbb,
  rw ←hbb at *,
  have : b = c,
    exact bet_same h6,
  exact h_7 this,
have h_21 : eqd c' p c' q,
  exact four17 h_20 h19 h_18 h_19,
have h20 : col c' c p,
  left, exact hp.1,
have h_22 : eqd p p p q,
  exact four17 (ne.symm h_10) h20 h_21 h15,
have h21 : p = q,
  exact id_eqd h_22.symm,
rw h21 at *,
have : d' = d,
  exact id_eqd h_13,
rw this at *,
left,
exact hd.1
end

theorem five2 {a b c d : point} : a ≠ b → B a b c → B a b d → B b c d ∨ B b d c :=
begin
intros h h1 h2,
cases five1 h h1 h2,
  left,
  exact three6a h1 h_1,
right,
exact three6a h2 h_1
end

theorem five3 {a b c d : point} : B a b d → B a c d → B a b c ∨ B a c b :=
begin
intros h h1,
cases three14 d a with p hp,
have h2 : B p a b,
  exact three5a hp.1.symm h,
have h3 : B p a c,
  exact three5a hp.1.symm h1,
cases five1 hp.2.symm h2 h3 with hb hc,
  left,
  exact three6a h2 hb,
right,
exact three6a h3 hc
end

theorem five4 {a b c d : point} : a ≠ b → col a b c → col a b d → col a c d :=
begin
intros h h1 h2,
cases h1,
  cases h2,
    cases five1 h h1 h2,
      left,
      assumption,
    right, left,
    exact h_1.symm,
  cases h2,
    right, left,
    exact (three6b h2.symm h1).symm,
  right, right,
  exact three7b h2 h1 h,
cases h1,
  cases h2,
    left,
    exact three6b h1.symm h2,
  cases h2,
    cases five3 h1.symm h2.symm,
      left,
      assumption,
    right, left,
    exact h_1.symm,
  right, right,
  exact three5a h2 h1.symm,
cases h2,
  right, right,
  exact (three7b h1 h2 h).symm,
cases h2,
  right, right,
  exact three6a h2 h1.symm,
cases five2 h.symm h1.symm h2.symm,
  left,
  assumption,
right, left,
exact h_1.symm
end

theorem five7 {a b x y z : point} : B a x b → B a z b → B x y z → B a y b :=
begin
intros h h1 h2,
cases five3 h h1,
  apply three6b _ h1,
  exact three5b h_1 h2,
apply three6b _ h,
exact three5b h_1 h2.symm
end

def distle (a b c d : point) : Prop := ∃ y, B c y d ∧ eqd a b c y

theorem five5 {a b c d : point} : distle a b c d ↔ ∃ x, B a b x ∧ eqd a x c d :=
begin
split,
  intro h,
  cases h with y hy,
  have : col c y d,
    left,
    exact hy.1,
  cases four14 this hy.2.symm with x hx,
  constructor,
    split,
    exact four6 hy.1 hx,
    exact hx.2.2.symm,
intro h,
cases h with x hx,
unfold distle,
have : col a x b,
  right, left,
  exact hx.1.symm,
cases four14 this hx.2 with y hy,
constructor,
  split,
    exact (four6 hx.1.symm (four4 hy).2.2.1).symm,
exact hy.2.2
end

theorem five6 {a b c d a' b' c' d' : point} : distle a b c d → eqd a b a' b' →
eqd c d c' d' → distle a' b' c' d' :=
begin
intros h h1 h2,
cases h with x hx,
cases four5 hx.1 h2 with y hy,
constructor,
  split,
  exact hy.1,
exact eqd.trans h1.symm (eqd.trans hx.2 hy.2.1)
end

theorem distle.refl (a b : point) : distle a b a b :=
begin
constructor,
  split,
    exact three1 a b,
exact eqd.refl a b
end

theorem distle.trans {a b c d e f : point} : distle a b c d → distle c d e f → distle a b e f :=
begin
intros h h1,
cases h with x hx,
cases h1 with y hy,
cases four5 hx.1 hy.2 with z hz,
constructor,
  split,
    exact three6b hz.1 hy.1,
exact eqd.trans hx.2 hz.2.1
end

theorem distle.flip {a b c d : point} : distle a b c d → distle b a d c :=
λ h, five6 h (two5 (eqd.refl a b)) (two5 (eqd.refl c d))

theorem five9 {a b c d : point} : distle a b c d → distle c d a b → eqd a b c d :=
begin
intros h h1,
cases h1 with x hx,
cases five5.mp h with z hz,
cases three14 b a with p hp,
cases hp with h1 h2,
rw three2 at h1,
cases em (a = b),
  rw h_1 at *,
  have : b = x,
    exact bet_same hx.1,
  rw this at *,
  exact hx.2.symm,
have h2 : p ≠ a,
  exact h2.symm,
have : x = z,
  exact two12 h2 (three5a h1 hx.1) hx.2.symm (three7b h1 hz.1 h_1) hz.2,
rw this at *,
have : b = z,
  exact three4 hx.1.symm hz.1.symm,
rw this at *,
exact hz.2
end

theorem five10 (a b c d : point) : distle a b c d ∨ distle c d a b :=
begin
cases three14 b a with p hp,
cases seg_cons a c d p with x hx,
cases five1 hp.2.symm hp.1.symm hx.1,
  have : B a b x,
    exact three6a hp.1.symm h,
  left,
  apply five5.mpr,
  constructor,
    split,
      exact this,
  exact hx.2,
  have : B a x b,
    exact three6a hx.1 h,
  right,
  constructor,
    split,
      exact this,
  exact hx.2.symm
end

theorem five11 (a b c : point) : distle a a b c :=
begin
cases five10 a a b c with h,
  assumption,
cases h with x hx,
have : a = x ,
  exact bet_same hx.1,
rw this at *,
have : b = c,
  exact id_eqd hx.2,
rw this at *,
existsi c,
split,
  exact three1 c c,
exact hx.2.symm
end

theorem five12 {a b c : point} : col a b c → (B a b c ↔ distle a b a c ∧ distle b c a c) :=
begin
intro h,
split,
  intro h1,
  split,
    constructor,
      split,
        exact h1,
    exact eqd.refl a b,
    have h2 : distle c b c a,
      constructor,
        split,
          exact h1.symm,
    exact eqd.refl c b,
  apply five6 h2,
    exact two5 (eqd.refl c b),
  exact two5 (eqd.refl c a),
intro h1,
cases h1 with h1 h2,
cases h1 with x hx,
have : distle c b c a,
  exact five6 h2 (two5 (eqd.refl b c)) (two5 (eqd.refl a c)),
cases this with y hy,
cases h with h,
  assumption,
cases h with h3 h4,
  rw three2 at h3,
  cases three14 b a with p hp,
  have : B p a c,
    exact three5a hp.1.symm h3,
  have : B p a x,
    exact three5a this hx.1,
  have : b = x,  
    exact two12 hp.2.symm hp.1.symm (eqd.refl a b) this hx.2.symm,
  rw ←this at *,
  exact hx.1,
rw three2 at h4,
cases three14 b c with q hq,
have : B q c a,
  exact three5a hq.1.symm h4.symm,
have : B q c y,
  exact three5a this hy.1,
 have : b = y,
  exact two12 hq.2.symm hq.1.symm (eqd.refl c b) this hy.2.symm,
rw ←this at *,
exact hy.1.symm
end

def distlt (a b c d : point) : Prop := distle a b c d ∧ ¬eqd a b c d

theorem five13 {a b c d : point} : distlt a b c d ↔ ∃ y, B c y d ∧ eqd a b c y ∧ y ≠ d :=
begin
split,
  rintros ⟨⟨y, hy⟩, h1⟩,
  refine ⟨y, hy.1, hy.2, _⟩,
  intro h_1,
  subst y,
  exact h1 hy.2,
rintros ⟨y, h, h1, h2⟩,
refine ⟨⟨y, h, h1⟩, _⟩,
intro h_1,
exact h2 (three15 h (h1.symm.trans h_1))
end

theorem five14 {a b c d a' b' c' d' : point} : distlt a b c d → eqd a b a' b' →
eqd c d c' d' → distlt a' b' c' d' :=
λ h h1 h2, ⟨five6 h.1 h1 h2, λ h_1, h.2 (h1.trans (h_1.trans h2.symm))⟩

theorem distlt.trans {a b c d e f : point} : distlt a b c d → distlt c d e f → distlt a b e f :=
λ h h1, ⟨h.1.trans h1.1, λ h_1, h.2 (five9 h.1 (five6 h1.1 (eqd.refl c d) h_1.symm))⟩

theorem distlt.flip {a b c d : point} : distlt a b c d → distlt b a d c :=
λ h, ⟨h.1.flip, λ h_1, h.2 h_1.flip⟩

theorem five15 {a b c d : point} : distlt a b c d → distlt c d a b → false :=
λ h h1, (h.trans h1).2 (eqd.refl a b)

theorem dist_lt_or_eq_of_le {a b c d : point} : distle a b c d → distlt a b c d ∨ eqd a b c d :=
begin
intro h,
cases em (eqd a b c d),
  exact or.inr h_1,
exact or.inl ⟨h, h_1⟩
end

theorem dist_lt_iff_not_le {a b c d : point} : distlt a b c d ↔ ¬distle c d a b :=
begin
split,
  intros h h1,
  exact h.2 (five9 h.1 h1),
intro h,
split,
  have h1 := five10 a b c d,
  simp [h] at h1,
  exact h1,
intro h1,
exact h (five6 (distle.refl a b) h1 (eqd.refl a b))
end

theorem dist_le_iff_not_lt {a b c d : point} : distle a b c d ↔ ¬distlt c d a b :=
begin
split,
  intros h h1,
  exact dist_lt_iff_not_le.1 h1 h,
intro h,
by_contradiction h_1,
exact h (dist_lt_iff_not_le.2 h_1)
end

theorem dist_total (a b c d : point) : distlt a b c d ∨ eqd a b c d ∨ distlt c d a b :=
begin
cases em (distle a b c d),
  cases dist_lt_or_eq_of_le h;
  simp *,
simp [dist_lt_iff_not_le.2 h]
end

-- Rays and Lines

def sided (p a b : point) : Prop := a ≠ p ∧ b ≠ p ∧ (B p a b ∨ B p b a)

theorem six1 {a b p : point} : col a p b → B a p b ∨ sided p a b :=
begin
intro h,
cases em (B a p b),
  exact or.inl h_1,
unfold col at h,
simp * at *,
rw [three2 b a p] at h,
refine ⟨_, _, h.symm⟩;
intro h_1;
subst p,
  exact h_1 (three3 a b),
exact h_1 (three1 a b)
end

theorem six2 {a b c p : point} : a ≠ p → b ≠ p → c ≠ p → B a p c → (B b p c ↔ sided p a b) :=
begin
intros h h1 h2 h3,
split,
  intro h4,
    unfold sided; repeat {split}; try {assumption},
  exact five2 h2 h3.symm h4.symm,
intro h4,
cases h4 with h h1,
cases h1 with h1 ha,
cases ha with ha hb,
  exact three7a ha.symm h3 h,
exact three6a hb.symm h3
end

theorem six3 {a b p : point} : sided p a b ↔ a ≠ p ∧ b ≠ p ∧ ∃ c, c ≠ p ∧ B a p c ∧ B b p c :=
begin
split,
  intro h,
  cases h with h h1,
  cases h1 with h1 h2,
  split, exact h,
    split, exact h1,
    cases three14 a p with c hc,
    constructor, split,
      exact hc.2.symm,
  split, exact hc.1,
  cases h2,
    exact three7a h2.symm hc.1 h,
  exact three6a h2.symm hc.1,
intro h,
cases h with h h1,
cases h1 with h1 h2,
split, exact h,
split, exact h1,
cases h2 with c h2,
exact five2 h2.1 h2.2.1.symm h2.2.2.symm
end

theorem six4 {a b p : point} : sided p a b ↔ col a p b ∧ ¬B a p b :=
begin
split,
  rintros ⟨h, h1, h2⟩,
  cases h2 with ha hb,
    split,
      unfold col,
      simp [ha.symm],
    intro h2,
    exact h (three4 h2 ha),
  split,
    unfold col,
    simp [hb],
  intro h2,
  exact h1 (three4 h2.symm hb),
rintros ⟨h, h1⟩,
split,
  intro h1,
  subst p,
  exact h1 (three3 a b),
split,
  intro h1,
  subst p,
  exact h1 (three1 a b),
unfold col at h,
simp [h1] at h,
rw [three2 b a p] at h,
exact h.symm
end

theorem six5 {a p : point} : a ≠ p → sided p a a :=
begin
intro h,
apply six4.2,
split,
  right, left,
  exact three1 p a,
intro h1,
exact h (bet_same h1)
end

theorem six6 {a b c d : point} : B a b c → sided b c d → B a b d :=
begin
intros h h1,
cases h1.2.2,
  exact three7b h h_1 h1.1.symm,
exact three5a h h_1
end

theorem six7 {a b p : point} : B p a b → a ≠ p → sided p a b :=
begin
intros h h1,
refine ⟨h1, _, or.inl h⟩,
intro h_1,
subst h_1,
exact h1.symm (bet_same h)
end

theorem sided.symm {a b p : point} : sided p a b → sided p b a :=
begin
intro h,
cases six3.1 h with h h1,
cases h1 with h1 h2,
cases h2 with c hc,
apply six3.2,
split, exact h1,
split, exact h,
constructor,
  split,
    exact hc.1,
split,
  exact hc.2.2,
exact hc.2.1
end

theorem sided.trans {a b c p : point} : sided p a b → sided p b c → sided p a c :=
begin
intros h1 h,
cases six3.1 h1 with h1 h2,
cases h2 with h2 h3,
cases h3 with q hq,
have h3 : c ≠ p,
  exact h.2.1,
have : B c p q,
  exact (six2 h2 h3 hq.1 hq.2.2).2 h,
exact (six2 h1 h3 hq.1 hq.2.1).1 this
end

theorem six6a {a b c d : point} : sided a b c → B b d c → sided a b d :=
begin
intros h h1,
cases h.2.2,
  exact six7 (three5a h_1 h1) h.1,
exact h.trans (six7 (three5a h_1 h1.symm) h.2.1)
end

theorem six7a {a b c p : point} : B p a b → sided p a c → sided p b c :=
begin
intros h h1,
apply sided.trans _ h1,
exact (six7 h h1.1).symm
end

theorem six8 {a b c p q : point} : sided b p a → sided b q c → B a b c → B p b q :=
begin
intros h h1 h2,
have h3 : B p b c,
  cases h.2.2,
    exact three6a h_1.symm h2,
  exact three7a h_1.symm h2 h.2.1,
cases h1.2.2,
  exact three5a h3 h_1,
exact three7b h3 h_1 h1.2.1.symm
end

def ray (p a : point) : set point := {x | sided p a x}

def hline (k : set point) : Prop := ∃ p a, a ≠ p ∧ k = ray p a

theorem six11 {a b c r : point} : r ≠ a → b ≠ c → ∃! x, sided a x r ∧ eqd a x b c :=
begin
intros h h1,
cases three14 r a with p hp,
cases seg_cons a b c p with x hx,
have h2 : x ≠ a,
  intro ha,
  rw ha at hx,
  have : b = c,
    exact id_eqd hx.2.symm,
  contradiction,
have h3 : sided a x r,
  split,
    exact h2,
  split,
    exact h,
  exact five2 hp.2.symm hx.1 hp.1.symm,
apply exists_unique.intro,
  exact ⟨h3, hx.2⟩,
intros y hy,
have : B p a y,
  exact ((six2 h2 hy.1.1 hp.2.symm hx.1.symm).2 (sided.trans h3 hy.1.symm)).symm,
exact two12 hp.2.symm this hy.2 hx.1 hx.2
end

theorem six11a {p a b : point} : sided p a b → eqd p a p b → a = b :=
λ h h1, unique_of_exists_unique (six11 h.1 h.1.symm) ⟨(six5 h.1), eqd.refl p a⟩ ⟨h.symm, h1.symm⟩

theorem six12 {a b p : point} : sided p a b → (distle p a p b ↔ B p a b) :=
begin
intro h1,
have hp : sided p a b, exact h1,
split,
  intro h,
  cases h1 with h1 h2,
  cases h2 with h2 h3,
  cases h3,
    exact h3,
  have : col p b a,
    left, exact h3,
  have : distle p b p a,
    exact ((five12 this).1 h3).1,
  have : eqd p a p b,
    exact five9 h this,
  cases three14 a p with q hq,
  have h4 : B q p b,
    exact ((six2 h1 h2 hq.2.symm hq.1).2 hp).symm,
  have : a = b,
    exact two12 hq.2.symm hq.1.symm (eqd.refl p a) h4 this.symm,
  rw this,
  exact three1 p b,
intro h,
unfold distle,
existsi a,
split,
  exact h,
exact eqd.refl p a
end

end Euclidean_plane