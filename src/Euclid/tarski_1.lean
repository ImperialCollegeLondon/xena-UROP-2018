import euclid.axioms
open classical
namespace Euclidean_plane

variables {point : Type} [Euclidean_plane point]

--Conclusions from the first 5 axioms
theorem eqd.refl (a b : point) : eqd a b a b :=
eqd_trans b a a b a b (eqd_refl b a) (eqd_refl b a)

theorem eqd.symm {a b c d : point} : eqd a b c d → eqd c d a b :=
assume h : eqd a b c d,
eqd_trans a b c d a b h (eqd.refl a b)

theorem eqd.trans {a b c d e f: point} : eqd a b c d → eqd c d e f → eqd a b e f :=
assume h h1,
eqd_trans c d a b e f h.symm h1

theorem two4 {a b c d : point} : eqd a b c d → eqd b a c d := assume h, eqd_trans a b b a c d (eqd_refl a b) h

theorem two5 {a b c d : point} : eqd a b c d → eqd a b d c := assume h, eqd.trans h (eqd_refl c d)

theorem eqd.flip {a b c d : point} : eqd a b c d → eqd b a d c := assume h, two4 (two5 h)

instance point_setoid : setoid (point × point) :=
{ r := λ ⟨a,b⟩ ⟨c,d⟩, eqd a b c d,
  iseqv := ⟨ λ ⟨a,b⟩, eqd.refl a b, λ ⟨a,b⟩ ⟨c,d⟩, eqd.symm, λ ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩, eqd.trans⟩
}
/-
definition distance_values (point : Type) [Euclidean_plane point] := 
quotient (@point_setoid point _)
-/
theorem refl_dist (a b : point) : (a,b) ≈ (b,a) := eqd_refl a b

theorem two8 (a b : point) : (a,a) ≈ (b,b) := 
let ⟨x, h⟩ := seg_cons a b b b in
have a = x, from id_eqd a x b h.2,
by rw ←this at h; exact h.2

def afs (a b c d a' b' c' d' : point) : Prop := B a b c ∧ B a' b' c' ∧ eqd a b a' b' 
∧ eqd b c b' c' ∧ eqd a d a' d' ∧ eqd b d b' d'

theorem afive_seg {a b c d a' b' c' d' : point} : afs a b c d a' b' c' d' → 
a ≠ b → eqd c d c' d' := 
begin
intros h h1,
apply five_seg a b c d a' b' c' d' h1,
  repeat {cases h with h2 h},
all_goals {assumption}
end

theorem two11 {a b c a' b' c' : point} : B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a c a' c' := 
begin
intros,
have : afs a b c a a' b' c' a',
  repeat {split}; try {assumption},
  exact two8 _ _,
  exact a_3.flip,
cases em (a = b),
  have : eqd a' b' a a,
    apply eqd.symm,
    rw ←h at a_3,
    assumption,
  have : a' = b',
    apply id_eqd,
    assumption,
  rw ←h at a_4,
  rw ←this at a_4,
  assumption,  
apply eqd.flip,
apply afive_seg this,
  assumption
end

theorem two12 (a b c q : point) : q ≠ a → ∃! x, B q a x ∧ eqd a x b c :=
begin
intro h,
cases seg_cons a b c q with x h1,
existsi x,
split,
  assumption,
intros y hy,
cases h1 with h2 h3,
cases hy with h4 h5,
apply by_contradiction,
intro h1,
have h6 : eqd a x a y,
  exact eqd_trans b c a x a y h3.symm h5.symm,
have h7 : eqd q x q y,
  apply two11 h2 h4,
    exact eqd.refl _ _,
  assumption,
have : afs q a x x q a x y,
  repeat {split}; try {assumption},
    exact eqd.refl _ _,
  exact eqd.refl _ _,
have : eqd x x x y,
  apply afive_seg this h,
have : x = y,
  exact id_eqd x y x this.symm,
have : y = x,
  exact eq.symm this,
contradiction
end

--Properties of Between

theorem three1 (a b : point) : B a b b := 
begin
cases seg_cons b b b a with x h,
have : b = x,
  exact id_eqd b x b h.2,
rw ←this at h,
exact h.1
end

theorem B.symm {a b c : point} : B a b c → B c b a :=
begin
intro h,
cases pasch a b c b c h (three1 b c) with x hx,
have : b = x,
  exact bet_same b x hx.1,
rw ←this at hx,
exact hx.2
end

theorem three2 {a b c : point} : B a b c ↔ B c b a :=
begin
apply iff.intro,
  exact B.symm,
intro h,
exact h.symm
end

theorem three3 (a b : point) : B a a b := 
begin
exact (three1 b a).symm
end

theorem three4 {a b c: point} : B a b c → B b a c → a = b :=
begin
intros h h1,
cases pasch a b c b a h h1 with x hx,
have : a = x,
  exact bet_same a x hx.2,
have : b = x,
  exact bet_same b x hx.1,
simp *
end

theorem three5a {a b c d : point} : B a b d → B b c d → B a b c:=
begin
intros h h1,
cases pasch a b d b c h h1 with x hx,
have : b = x,
  exact bet_same b x hx.1,
rw ←this at hx,
exact hx.2.symm,
end

theorem three6a {a b c d : point} : B a b c → B a c d → B b c d :=
begin
intros h h1,
exact (three5a h1.symm h.symm).symm
end

theorem three7a {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a c d :=
begin
intros h h1 h2,
cases seg_cons c c d a with x hx,
have : B b c x,
  exact three6a h hx.1,
cases two12 c c d b h2 with y hy,
have : x = y,
  apply hy.2,
  split,
    exact this, exact hx.2,
have : d = y,
  apply hy.2,
  split,
    exact h1, exact eqd.refl c d,
have : x = d,
  simp *,
rw this at hx,
exact hx.1
end

theorem three5b {a b c d : point} : B a b d → B b c d → B a c d :=
begin
intros h h1,
cases em (b = c),
  rwa h_1 at h,
exact three7a (three5a h h1) h1 h_1
end

theorem three6b {a b c d : point} : B a b c → B a c d → B a b d :=
begin
intros h h1,
cases em (c = b),
  rwa h_1 at h1,
exact (three7a (three6a h h1).symm h.symm h_1).symm
end

theorem three7b {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a b d :=
begin
intros h h1 h2,
have h3 : B a c d,
  exact three7a h h1 h2,
exact (three5b h3.symm h.symm).symm
end

theorem three13 : ∃ (x y : point), x ≠ y := 
let ⟨a, b, c, hp⟩ := (two_dim point) in
begin
have : a ≠ b,
  intro h,
  have : B a b c,
    rw h,
    exact three3 b c,
  exact hp.1 this,
constructor, exact ⟨b, this⟩
end

theorem three14 (a b : point) : ∃ c, B a b c ∧ b ≠ c := 
let ⟨(x : point), y, hp⟩ := three13 in
begin
cases seg_cons b x y a with c h,
cases h with h1 h2,
have : b ≠ c,
  intro hq,
  have : eqd x y b b,
    apply eqd.symm,
    rwa ←hq at h2,
  exact hp (id_eqd x y b this) ,
constructor, exact ⟨h1, this⟩
end

theorem three17 {a b c a' b' p : point} : B a b c → B a' b' c 
→ B a p a' → ∃ q, B p q c ∧ B b q b' := 
begin
intros h1 h2 h3,
cases pasch a c a' p b' h3 h2.symm with x h4,
cases pasch c b' a b x h1.symm h4.2 with y h5,
have : B p y c,
  exact three5b h4.1 h5.2,
constructor, exact ⟨this, h5.1⟩
end

-- Statements about eqd + B

def ifs (a b c d a' b' c' d' : point) : Prop := B a b c ∧ B a' b' c' ∧ eqd a c a' c' 
∧ eqd b c b' c' ∧ eqd a d a' d' ∧ eqd c d c' d'

theorem four2 {a b c d a' b' c' d' : point} : ifs a b c d a' b' c' d' → eqd b d b' d' :=
begin
intro h,
cases h with h h1,
cases h1 with h1 h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
cases h4 with h4 h5,
cases em (a = c),
  have : a' = c',
    have : eqd c c a' c',
      rwa h_1 at h2,
    exact id_eqd a' c' c this.symm,
  have h6 : c = b,
    apply bet_same c b,
    rwa h_1 at h,
  have h7 : b' = c',
    have : eqd b b b' c',
      rwa h6 at h3,
    exact id_eqd b' c' b this.symm,
  rw [h6, ←h7] at h5,
  exact h5,
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
have : afs e c b d e' c' b' d',
  repeat {split};
    try{assumption},
    exact (three6a h he.1).symm,
    exact (three6a h1 he'.1).symm,
    exact he'.2.symm.flip,
  exact h3.flip,
exact afive_seg this he.2.symm
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

lemma four4 {a b c a' b' c' : point} : cong a b c a' b' c' → cong b c a b' c' a' :=
begin
intro h,
cases h with h h1,
cases h1 with h1 h2,
unfold cong,
repeat {split},
  assumption,
  exact h2.flip,
exact h.flip
end

theorem four5 {a b c a' c' : point} : B a b c → eqd a c a' c' 
→ ∃ b', B a' b' c' ∧ cong a b c a' b' c' :=
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
  apply unique_of_exists_unique (two12 a' a c d' hd.2.symm),
    split,
      exact hd.1.symm,
      exact h1.symm,
  split,
    exact h2.2,
  exact h3,
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
  exact id_eqd b'' b' b'' h4.symm,
rwa this at *
end

def col (a b c : point) : Prop := B a b c ∨ B b c a ∨ B c a b

theorem four11 {a b c : point} : col a b c → col a c b ∧ col b a c ∧ col b c a ∧ col c a b ∧ col c b a := 
begin
intro h,
cases h with h1 h2,
have : B c b a, exact h1.symm,
repeat {split}; unfold col;
  simp *,
cases h2 with h2 h3,
have : B a c b, exact h2.symm,
  repeat {split};unfold col;
  simp *,
have : B b a c, exact h3.symm,
repeat {split};unfold col;
  simp *
end

theorem four12 (a b : point) : col a a b := 
begin
unfold col,
left, exact three3 a b
end

theorem four13 {a b c a' b' c' : point} : col a b c → cong a b c a' b' c' → col a' b' c' :=
begin
intros h h1,
unfold col,
cases h,
  have : B a' b' c', exact four6 h h1,
  simp *,
cases h,
  have : B b' c' a', exact four6 h (four4 h1),
  simp *,
have : B c' a' b', exact four6 h (four4 (four4 h1)),
  simp *,
end

theorem four14 {a b c a' b' : point} : col a b c → eqd a b a' b' → ∃ c', cong a b c a' b' c' :=
begin
intros h1 h,
cases h1 with h1 h2,
cases seg_cons b' b c a' with c' hc,
  existsi c',
  unfold cong,
  split,
    exact h,
  split,
    exact hc.2.symm,
  exact two11 h1 hc.1 h hc.2.symm,
cases h2 with h2 h3,
  cases four5 h2 h.flip with c' hc,
  constructor, exact four4 (four4 hc.2),
cases seg_cons a' a c b' with c' hc,
existsi c',
unfold cong,
split,
  exact h,
split,
  exact two11 h3.symm hc.1 h.flip hc.2.symm,
exact hc.2.symm
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
  exact five_seg a b c d a' b' c' d' h ha (four6 ha h2) h2.1 h2.2.1 h3 h4,
cases hbc with hb hc,
  have : ifs b c a d b' c' a' d',
    repeat {split};
      try {assumption},
        exact four6 hb (four4 h2),
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
exact five_seg b a c d b' a' c' d' h.symm hc (four6 hc this) h2.1.flip h2.2.2 h4 h3
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
exact id_eqd c c' c this.symm
end

theorem four19 {a b c b' : point} : B a b c → eqd a b a b' → eqd b c b' c → b = b' :=
begin
intros h h1 h2,
cases em (a = c) with h3 h4,
  rw ←h3 at *,
  have : a = b, exact bet_same a b h,
  rw this at *,
  exact id_eqd b b' b h1.symm,
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
    exact id_eqd c d d hc.2.symm.flip,
  contradiction,
have h_3 : d' ≠ c,
  intro h_3,
  rw h_3 at hd,
  have : c = d,
    exact id_eqd c d c hd.2.symm,
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
  apply unique_of_exists_unique (two12 b b b' a h),
    split,
      exact h_5,
    exact eqd.refl b b',
  split,
    exact h_6,
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
cases pasch d' c' a c d hd.1.symm hc.1.symm with e he,
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
    exact id_eqd d' d d' h_9,
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
    exact id_eqd c e c hr.2.symm,
  rw ←this at *,
  have : c = c',
    exact id_eqd c c' c h_8.symm,
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
    exact bet_same b c h6,
  exact h_7 this,
have h_21 : eqd c' p c' q,
  exact four17 h_20 h19 h_18 h_19,
have h20 : col c' c p,
  left, exact hp.1,
have h_22 : eqd p p p q,
  exact four17 (ne.symm h_10) h20 h_21 h15,
have h21 : p = q,
  exact id_eqd p q p h_22.symm,
rw h21 at *,
have : d' = d,
  exact id_eqd d' d q h_13,
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

def distle (a b c d : point) : Prop := ∃ y, B c y d ∧ eqd a b c y

def distge (a b c d : point) : Prop := distle c d a b

theorem five5 {a b c d : point} : distle a b c d ↔ ∃ x, B a b x ∧ eqd a x c d :=
begin
apply iff.intro,
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
    exact (four6 hx.1.symm (four4 hy)).symm,
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

theorem five7 (a b : point) : distle a b a b :=
begin
constructor,
  split,
    exact three1 a b,
exact eqd.refl a b
end

theorem five8 {a b c d e f : point} : distle a b c d → distle c d e f → distle a b e f :=
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
    exact bet_same b x hx.1,
  rw this at *,
  exact hx.2.symm,
have h2 : p ≠ a,
  exact h2.symm,
have : x = z,
  apply unique_of_exists_unique (two12 a c d p h2),
    split,
    exact three5a h1 hx.1,
    exact hx.2.symm,
  split,
    exact three7b h1 hz.1 h_1,
  exact hz.2,
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
  exact bet_same a x hx.1,
rw this at *,
have : b = c,
  exact id_eqd b c x hx.2,
rw this at *,
existsi c,
split,
  exact three1 c c,
exact hx.2.symm
end

theorem five12 {a b c : point} : col a b c → (B a b c ↔ distle a b a c ∧ distle b c a c) :=
begin
intro h,
apply iff.intro,
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
    apply unique_of_exists_unique (two12 a a b p hp.2.symm),
      split,
        exact hp.1.symm,
      exact eqd.refl a b,
    split,
      exact this,
    exact hx.2.symm,
  rw ←this at *,
  exact hx.1,
rw three2 at h4,
cases three14 b c with q hq,
have : B q c a,
  exact three5a hq.1.symm h4.symm,
have : B q c y,
  exact three5a this hy.1,
 have : b = y,
  apply unique_of_exists_unique (two12 c c b q hq.2.symm),
    split,
      exact hq.1.symm,
    exact eqd.refl c b,
  split,
    exact this,
  exact hy.2.symm,
rw ←this at *,
exact hy.1.symm
end

-- Rays and Lines

def sided (p a b : point) : Prop := a ≠ p ∧ b ≠ p ∧ (B p a b ∨ B p b a)

theorem six2 {a b c p : point} : a ≠ p → b ≠ p → c ≠ p → B a p c → (B b p c ↔ sided p a b) :=
begin
intros h h1 h2 h3,
apply iff.intro,
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
apply iff.intro,
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
apply iff.intro,
  intro h,
  cases h with h h1,
  cases h1 with h1 h2,
  cases h2 with ha hb,
    split,
      unfold col,
      simp [ha.symm],
    intro h2,
    have : a = p,
      exact three4 h2 ha,
    contradiction,
  split,
    unfold col,
    simp [hb],
  intro h2,
  have : b = p,
    exact three4 h2.symm hb,
  contradiction,
intro h,
unfold sided,
split,
  intro ha,
  rw ha at *,
  have : B p p b,
    exact three3 p b,
  exact h.2 this,
split,
  intro hb,
  rw hb at *,
  have : B a p p,
    exact three1 a p,
  exact h.2 this,
cases h with h h1,
cases h,
  contradiction,
cases h,
  right, exact h,
left,
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
have : a = p,
  exact bet_same a p h1,
contradiction
end

theorem six6 {a b p : point} : sided p a b → sided p b a :=
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

theorem six7 {a b c p : point} : sided p a b → sided p b c → sided p a c :=
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
    exact id_eqd b c a hx.2.symm,
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
  exact ((six2 h2 hy.1.1 hp.2.symm hx.1.symm).2 (six7 h3 (six6 hy.1))).symm,
apply unique_of_exists_unique (two12 a b c p hp.2.symm),
  exact ⟨this, hy.2⟩,
exact hx
end

theorem six13 {a b p : point} : sided p a b → (distle p a p b ↔ B p a b) :=
begin
intro h1,
have hp : sided p a b, exact h1,
apply iff.intro,
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
    apply unique_of_exists_unique (two12 p p a q hq.2.symm),
      split,
        exact hq.1.symm,
      exact eqd.refl p a,
    split,
      exact h4,
    exact this.symm,
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