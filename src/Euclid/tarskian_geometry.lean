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

theorem twopoint4 {a b c d : point} : eqd a b c d → eqd b a c d := assume h, eqd_trans a b b a c d (eqd_refl a b) h

theorem twopoint5 {a b c d : point} : eqd a b c d → eqd a b d c := assume h, trans_eqd h (eqd_refl c d)

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

theorem twopoint8 (a b : point) : (a,a) ≈ (b,b) := 
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

theorem twopoint11 (a b c a' b' c' : point) : B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a c a' c' := 
begin
intros,
have : afs a b c a a' b' c' a',
  repeat {split}; try {assumption},
  exact twopoint8 _ _,
  exact twopoint4 (twopoint5 a_3),
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
apply twopoint4 (twopoint5 _),
apply afive_seg this,
  assumption
end

theorem twopoint12 (a b c q : point) : q ≠ a → ∃! x, B q a x ∧ eqd a x b c :=
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
  apply twopoint11 q a x q a y h2 h4,
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

theorem threepoint1 (a b : point) : B a b b := 
begin
cases seg_cons b b b a with x h,
have : b = x,
  exact id_eqd b x b h.right,
rw ←this at h,
exact h.left
end

theorem betswap {a b c: point} : B a b c → B c b a :=
begin
intro h,
cases pasch a b c b c h (threepoint1 b c) with x hx,
have : b = x,
  exact bet_same b x hx.left,
rw ←this at hx,
exact hx.right
end

theorem threepoint3 (a b : point) : B a a b := 
begin
exact betswap (threepoint1 b a)
end

theorem threepoint4 {a b c: point} : B a b c → B b a c → a = b :=
begin
intros h h1,
cases pasch a b c b a h h1 with x hx,
have : a = x,
  exact bet_same a x hx.right,
have : b = x,
  exact bet_same b x hx.left,
simp *
end

theorem threepoint5a {a b c d : point} : B a b d → B b c d → B a b c:=
begin
intros h h1,
cases pasch a b d b c h h1 with x hx,
have : b = x,
  exact bet_same b x hx.left,
rw ←this at hx,
exact betswap hx.right,
end

theorem threepoint6a {a b c d : point} : B a b c → B a c d → B b c d :=
begin
intros h h1,
exact betswap (threepoint5a (betswap h1) (betswap h))
end

theorem threepoint7a {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a c d :=
begin
intros h h1 h2,
cases seg_cons c c d a with x hx,
have : B b c x,
  exact threepoint6a h hx.left,
cases twopoint12 c c d b h2 with y hy,
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

theorem threepoint5b {a b c d : point} : B a b d → B b c d → B a c d :=
begin
intros h h1,
cases em (b = c),
  rwa h_1 at h,
exact threepoint7a (threepoint5a h h1) h1 h_1
end

theorem threepoint6b {a b c d : point} : B a b c → B a c d → B a b d :=
begin
intros h h1,
cases em (c = b),
  rwa h_1 at h1,
exact betswap (threepoint7a (betswap (threepoint6a h h1)) (betswap h) h_1)
end

theorem threepoint7b {a b c d : point} : B a b c → B b c d → b ≠ c 
→ B a b d :=
begin
intros h h1 h2,
have h3 : B a c d,
  exact threepoint7a h h1 h2,
exact betswap (threepoint5b (betswap h3) (betswap h))
end

theorem threepoint13 : ∃ (x y : point), x ≠ y := 
let ⟨a, b, c, hp⟩ := (two_dim point) in
begin
have : a ≠ b,
  intro h,
  have : B a b c,
    rw h,
    exact threepoint3 b c,
  exact hp.left this,
constructor, exact ⟨b, this⟩
end

theorem threepoint14 (a b : point) : ∃ c, B a b c ∧ b ≠ c := 
let ⟨(x : point), (y : point), hp⟩ := threepoint13 in
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

theorem threepoint17 (a b c a' b' p : point) : B a b c → B a' b' c 
→ B a p a' → ∃ q, B p q c ∧ B b q b' := 
begin
intros h1 h2 h3,
cases pasch a c a' p b' h3 (betswap h2) with x h4,
cases pasch c b' a b x (betswap h1) h4.right with y h5,
have : B p y c,
  exact threepoint5b h4.left h5.right,
constructor, exact ⟨this, h5.left⟩
end

-- Statements about eqd + B
