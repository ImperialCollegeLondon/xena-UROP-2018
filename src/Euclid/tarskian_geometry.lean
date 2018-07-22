import euclid.axioms
open Euclidean_plane
open classical


variables {point : Type} [Euclidean_plane point]
--Conclusions from the first 5 axioms
theorem refl_eqd (a b : point) : eqd a b a b :=
eqd_trans b a a b a b (eqd_refl b a) (eqd_refl b a)

theorem symm_eqd {a b c d : point} : eqd a b c d → eqd c d a b :=
assume h : eqd a b c d,
eqd_trans a b c d a b h (refl_eqd a b)

theorem trans_eqd {a b c d e f: point} : eqd a b c d → eqd c d e f → eqd a b e f :=
assume h h1,
eqd_trans c d a b e f (symm_eqd h) h1

theorem two4 {a b c d : point} : eqd a b c d → eqd b a c d := assume h, eqd_trans a b b a c d (eqd_refl a b) h

theorem two5 {a b c d : point} : eqd a b c d → eqd a b d c := assume h, trans_eqd h (eqd_refl c d)

theorem eqdflip {a b c d : point} : eqd a b c d → eqd b a d c := assume h, two4 (two5 h)

-- a "setoid" is just a silly computer science name for a type with an equiv reln
instance point_setoid : setoid (point × point) :=
{ r := λ ⟨a,b⟩ ⟨c,d⟩, eqd a b c d,
  iseqv := ⟨ λ ⟨a,b⟩, refl_eqd a b, λ ⟨a,b⟩ ⟨c,d⟩, symm_eqd, λ ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩, trans_eqd⟩
}

-- this type denotes the equiv classes. You may never need it but it's
-- a good test to see if you've got the definitions right!
definition distance_values (point : Type) [Euclidean_plane point] := 
quotient (@point_setoid point _)



theorem refl_dist (a b : point) : (a,b) ≈ (b,a) := eqd_refl a b

theorem two8 (a b : point) : (a,a) ≈ (b,b) := 
let ⟨x, h⟩ := seg_cons a b b b in
have a = x, from id_eqd a x b h.right,
by rw ←this at h; exact h.right

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
  exact eqdflip a_3,
cases em (a = b),
  have : eqd a' b' a a,
    apply symm_eqd,
    rw ←h at a_3,
    assumption,
  have : a' = b',
    apply id_eqd,
    assumption,
  rw ←h at a_4,
  rw ←this at a_4,
  assumption,  
apply eqdflip _,
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
  exact eqd_trans b c a x a y (symm_eqd h3) (symm_eqd h5),
have h7 : eqd q x q y,
  apply two11 h2 h4,
    exact refl_eqd _ _,
  assumption,
have : afs q a x x q a x y,
  repeat {split}; try {assumption},
    exact refl_eqd _ _,
  exact refl_eqd _ _,
have : eqd x x x y,
  apply afive_seg this h,
have : x = y,
  exact id_eqd x y x (symm_eqd this),
have : y = x,
  exact eq.symm this,
contradiction
end

--Properties of Between

theorem three1 (a b : point) : B a b b := 
begin
cases seg_cons b b b a with x h,
have : b = x,
  exact id_eqd b x b h.right,
rw ←this at h,
exact h.left
end

theorem betswap {a b c : point} : B a b c → B c b a :=
begin
intro h,
cases pasch a b c b c h (three1 b c) with x hx,
have : b = x,
  exact bet_same b x hx.left,
rw ←this at hx,
exact hx.right
end

theorem three2 {a b c : point} : B a b c ↔ B c b a :=
begin
apply iff.intro,
  exact betswap,
intro h,
exact betswap h
end


theorem three3 (a b : point) : B a a b := 
begin
exact betswap (three1 b a)
end

theorem three4 {a b c: point} : B a b c → B b a c → a = b :=
begin
intros h h1,
cases pasch a b c b a h h1 with x hx,
have : a = x,
  exact bet_same a x hx.right,
have : b = x,
  exact bet_same b x hx.left,
simp *
end

theorem three5a {a b c d : point} : B a b d → B b c d → B a b c:=
begin
intros h h1,
cases pasch a b d b c h h1 with x hx,
have : b = x,
  exact bet_same b x hx.left,
rw ←this at hx,
exact betswap hx.right,
end

theorem three6a {a b c d : point} : B a b c → B a c d → B b c d :=
begin
intros h h1,
exact betswap (three5a (betswap h1) (betswap h))
end

theorem three7a {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a c d :=
begin
intros h h1 h2,
cases seg_cons c c d a with x hx,
have : B b c x,
  exact three6a h hx.left,
cases two12 c c d b h2 with y hy,
have : x = y,
  apply hy.right,
  split,
    exact this, exact hx.right,
have : d = y,
  apply hy.right,
  split,
    exact h1, exact refl_eqd c d,
have : x = d,
  simp *,
rw this at hx,
exact hx.left
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
exact betswap (three7a (betswap (three6a h h1)) (betswap h) h_1)
end

theorem three7b {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a b d :=
begin
intros h h1 h2,
have h3 : B a c d,
  exact three7a h h1 h2,
exact betswap (three5b (betswap h3) (betswap h))
end

theorem three13 : ∃ (x y : point), x ≠ y := 
let ⟨a, b, c, hp⟩ := (two_dim point) in
begin
have : a ≠ b,
  intro h,
  have : B a b c,
    rw h,
    exact three3 b c,
  exact hp.left this,
constructor, exact ⟨b, this⟩
end

theorem three14 (a b : point) : ∃ c, B a b c ∧ b ≠ c := 
let ⟨(x : point), (y : point), hp⟩ := three13 in
begin
cases seg_cons b x y a with c h,
cases h with h1 h2,
have : b ≠ c,
  intro hq,
  have : eqd x y b b,
    apply symm_eqd,
    rwa ←hq at h2,
  exact hp (id_eqd x y b this) ,
constructor, exact ⟨h1, this⟩
end

theorem three17 {a b c a' b' p : point} : B a b c → B a' b' c 
→ B a p a' → ∃ q, B p q c ∧ B b q b' := 
begin
intros h1 h2 h3,
cases pasch a c a' p b' h3 (betswap h2) with x h4,
cases pasch c b' a b x (betswap h1) h4.right with y h5,
have : B p y c,
  exact three5b h4.left h5.right,
constructor, exact ⟨this, h5.left⟩
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
    exact id_eqd a' c' c (symm_eqd this),
  have h6 : c = b,
    apply bet_same c b,
    rwa h_1 at h,
  have h7 : b' = c',
    have : eqd b b b' c',
      rwa h6 at h3,
    exact id_eqd b' c' b (symm_eqd this),
  rw [h6, ←h7] at h5,
  exact h5,
cases three14 a c with e he,
cases seg_cons c' c e a' with e' he',
have : afs a c e d a' c' e' d',
  repeat {split};
    try{assumption},
    exact he.left,
    exact he'.left,
  exact symm_eqd he'.right,
have : eqd e d e' d',
  exact afive_seg this h_1,
have : afs e c b d e' c' b' d',
  repeat {split};
    try{assumption},
    exact betswap (three6a h he.left),
    exact betswap (three6a h1 he'.left),
    exact symm_eqd (eqdflip he'.right),
  exact eqdflip h3,
exact afive_seg this (ne.symm he.right)
end

theorem four3 {a b c a' b' c' : point} : B a b c → B a' b' c' → eqd a c a' c' 
→ eqd b c b' c' → eqd a b a' b' :=
begin
intros h h1 h2 h3,
  have : ifs a b c a a' b' c' a',
  repeat {split};
    try{assumption},
    exact two8 a a',
  exact (eqdflip h2),
exact (eqdflip (four2 this))
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
  exact (eqdflip h2),
exact (eqdflip h)
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
    exact three6a hb.left hc.left,
  exact three6b hb.left hc.left,
have h3 : eqd a' c'' a c,
  exact two11 h2.left h hb.right hc.right,
have h4 : c' = c'',
  apply unique_of_exists_unique (two12 a' a c d' (ne.symm hd.right)),
    split,
      exact betswap hd.left,
      exact symm_eqd h1,
  split,
    exact h2.right,
  exact h3,
rw ←h4 at *,
existsi b',
split,
  exact h2.left,
unfold cong,
split,
  apply four3 h h2.left,
    exact symm_eqd h3,
  exact symm_eqd hc.right,
split,
  exact symm_eqd hc.right,
exact symm_eqd h3
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
    exact trans_eqd (symm_eqd hb3) h3,
    exact refl_eqd _ _,
    exact trans_eqd (symm_eqd hb1) h1,
    have : eqd b'' c' b' c',
      exact trans_eqd (symm_eqd hb2) h2,
    exact (eqdflip this),
have : b'' = b',
  have h4 : eqd b'' b'' b'' b',
    exact four2 this,
  exact id_eqd b'' b' b'' (symm_eqd h4),
rwa this at *
end

def col (a b c : point) : Prop := B a b c ∨ B b c a ∨ B c a b

theorem four11 {a b c : point} : col a b c → col a c b ∧ col b a c ∧ col b c a ∧ col c a b ∧ col c b a := 
begin
intro h,
cases h with h1 h2,
have : B c b a, exact betswap h1,
repeat {split}; unfold col;
  simp *,
cases h2 with h2 h3,
have : B a c b, exact betswap h2,
  repeat {split};unfold col;
  simp *,
have : B b a c, exact betswap h3,
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
    exact symm_eqd hc.right,
  exact two11 h1 hc.left h (symm_eqd hc.right),
cases h2 with h2 h3,
  cases four5 h2 (eqdflip h) with c' hc,
  constructor, exact four4 (four4 hc.right),
cases seg_cons a' a c b' with c' hc,
existsi c',
unfold cong,
split,
  exact h,
split,
  exact two11 (betswap h3) hc.left (eqdflip h) (symm_eqd hc.right),
exact symm_eqd hc.right
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
      exact eqdflip h2.1,
    exact eqdflip h2.2.2,
  exact four2 this,
rw three2 at hc,
have : cong b a c b' a' c',
  unfold cong,
  split,
    exact eqdflip h2.1,
  split,
    exact h2.2.2,
  exact h2.2.1,
exact five_seg b a c d b' a' c' d' (ne.symm h) hc (four6 hc this) (eqdflip h2.1) h2.2.2 h4 h3
end

theorem four17 {a b c p q : point} : a ≠ b → col a b c → eqd a p a q → eqd b p b q → eqd c p c q :=
begin
intros h h1 h2 h3,
have : fs a b c p a b c q,
  unfold fs,
  repeat {split}; try {assumption};
  exact refl_eqd _ _,
exact four16 this h
end

theorem four18 {a b c c' : point} : a ≠ b → col a b c → eqd a c a c' → eqd b c b c' → c = c':=
begin
intros h h3 h1 h2,
have : eqd c c c c',
  exact four17 h h3 h1 h2,
exact id_eqd c c' c (symm_eqd this)
end

theorem four19 {a b c c' : point} : B a c b → eqd a c a c' → eqd b c b c' → c = c' :=
begin
intros h h1 h2,
cases em (a = b) with h3 h4,
  rw ←h3 at *,
  have : a = c, exact bet_same a c h,
  rw this at *,
  exact id_eqd c c' c (symm_eqd h1),
have : col a b c,
  right, left,
  exact betswap h,
exact four18 h4 this h1 h2
end

-- Relationship between B and distance comparison

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
    exact id_eqd c d d (symm_eqd (eqdflip hc.2)),
  contradiction,
have h_3 : d' ≠ c,
  intro h_3,
  rw h_3 at hd,
  have : c = d,
    exact id_eqd c d c (symm_eqd hd.2),
  contradiction,
have h3 : B b d c',
  exact three6a h2 hc.1,
have h4 : eqd b c' b'' c,
  exact two11 h3 (betswap hb.1) (symm_eqd (eqdflip hb.2)) (trans_eqd hc.2 (symm_eqd (eqdflip hd.2))),
have h5 : B b c' b',
  exact three7a h3 ha.1 h_2,
have h_4 : B b c d',
  exact three6a h1 hd.1,
have h6 : B b'' c b,
  exact three7a (betswap hb.1) (betswap h_4) h_3,
have h7 : eqd b b' b'' b,
  exact two11 h5 h6 h4 ha.2,
have h_5 : B a b b',
  have : B a d b',
    exact three7b hc.1 ha.1 h_2,
  exact three6b h2 this,
have h_6 : B a b b'',
  have : B a c b'',
    exact three7b hd.1 hb.1 (ne.symm h_3),
  exact three6b h1 this,
have h8 : b' = b'',
  apply unique_of_exists_unique (two12 b b b' a h),
    split,
      exact h_5,
    exact refl_eqd b b',
  split,
    exact h_6,
  exact two4 (symm_eqd h7),
rw ←h8 at *,
have h9 : afs b c d' c' b' c' d c,
  repeat {split}; try {assumption},
    exact betswap ha.1,
    exact (symm_eqd (eqdflip ha.2)),
    exact trans_eqd hd.2 (symm_eqd (eqdflip hc.2)),
  exact two5 (refl_eqd c c'),
cases em (b = c),
  left,
  rw ←h_7, exact h2,
have h10 : eqd c d c' d',
  exact symm_eqd (eqdflip (afive_seg h9 h_7)),
cases pasch d' c' a c d (betswap hd.1) (betswap hc.1) with e he,
have h11 : ifs d e d' c d e d' c',
  repeat {split}; try {assumption},
    exact he.right,
    exact he.right,
    exact refl_eqd d d',
    exact refl_eqd e d',
    exact symm_eqd hc.2,
  exact trans_eqd (eqdflip hd.2) (eqdflip h10),
have h12 : ifs c e c' d c e c' d',
  repeat {split}; try {assumption},
    exact he.1,
    exact he.1,
    exact refl_eqd c c',
    exact refl_eqd e c',
    exact symm_eqd hd.2,
  exact trans_eqd (eqdflip hc.2) h10,
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
    exact three5a (betswap hp.1) he.1,
    exact (symm_eqd (eqdflip hp.2)),
    exact hr.2,
    exact two4 (refl_eqd p d'),
  exact hp.2,
have h_11 : eqd r p e d',
  exact afive_seg h13 h_3,
have h_12 : eqd r q e d,
  exact trans_eqd hq.2 (trans_eqd h_11 (symm_eqd h_9)),
have h14 : afs d' e d c p r q c,
  repeat {split},
    exact betswap he.2,
    exact hq.1,
    exact (symm_eqd (eqdflip h_11)),
    exact symm_eqd h_12,
    exact (symm_eqd (eqdflip hp.2)),
  exact (symm_eqd (eqdflip hr.2)),
have h_13 : eqd d' d p q,
  exact two11 (betswap he.2) hq.1 (symm_eqd (eqdflip h_11)) (symm_eqd h_12),
cases em (d' = e),
  rw ←h_14 at *,
  have : d' = d,
    exact id_eqd d' d d' h_9,
  rw this at *,
  left, exact hd.1,
have h_15 : eqd c q c d,
  exact (symm_eqd (eqdflip (afive_seg h14 h_14))),
have h15 : eqd c p c q,
  exact trans_eqd hp.2 (trans_eqd hd.2 (symm_eqd h_15)),
have h_16 : r ≠ c,
  intro hrc,
  rw hrc at *,
  have : c = e,
    exact id_eqd c e c (symm_eqd hr.2),
  rw ←this at *,
  have : c = c',
    exact id_eqd c c' c (symm_eqd h_8),
  exact h_10 this,
have h16 : col r c d',
  left, exact betswap hr.1,
have h_17 : eqd d' p d' q,
  exact four17 h_16 h16 (symm_eqd hq.2) h15,
have h17 : col c d' b,
  right, right, exact h_4,
have h18 : col c d' b',
  left, exact hb.1,
have h_18 : eqd b p b q,
  exact four17 (ne.symm h_3) h17 h15 h_17,
have h_19 : eqd b' p b' q,
  exact four17 (ne.symm h_3) h18 h15 h_17,
have h19 : col b b' c',
  right, left, exact betswap h5,
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
  exact id_eqd p q p (symm_eqd h_22),
rw h21 at *,
have : d' = d,
  exact id_eqd d' d q h_13,
rw this at *,
left,
exact hd.1    
end
