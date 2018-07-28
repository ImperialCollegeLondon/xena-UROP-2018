import Euclid.tarski_2
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

local attribute [instance] prop_decidable

-- Right Angles

def R (a b c : point) : Prop := eqd a c a (S b c)

theorem R.symm {a b c : point} : R a b c → R c b a :=
begin
intro h,
let h1 := seven13 b a (S b c),
simp at h1,
unfold R at h,
exact (eqd.trans h h1).flip
end

theorem eight3 {a b c a' : point} : R a b c → a ≠ b → col b a a' → R a' b c :=
begin
intros h h1 h2,
unfold R at *,
let h3 := seven5 b c,
exact four17 h1.symm h2 h3.2 h
end

theorem R.flip {a b c : point} : R a b c → R a b (S b c) :=
begin
intro h,
unfold R at *,
simp,
exact h.symm
end

theorem eight5 (a b : point) : R a b b :=
begin
unfold R,
simp,
exact eqd.refl a b
end

theorem eight6 {a b c a' : point} : R a b c → R a' b c → B a c a' → b = c :=
begin
intros h h1 h2,
unfold R at *,
generalize h3 : S b c = c',
rw h3 at *,
have : c = c',
  exact four19 h2 h h1.flip,
rw ←this at *,
exact (seven10.1 h3).symm
end

theorem eight7 {a b c : point} : R a b c → R a c b → b = c :=
begin
intros h h1,
have h_1 : eqd a c a (S b c),
  unfold R at h,
  exact h,
have h_2 : eqd a b a (S c b),
  unfold R at h1,
  exact h1,
let h2 := seven5 b c,
generalize h3 : S b c = c',
rw h3 at *,
generalize h4 : S c a = a',
by_contradiction h5,
have h6 : col c b c',
  left,
  exact h2.1,
let h7 := eight3 h1.symm h5 h6,
unfold R at h7,
rw h4 at h7,
let h8 := seven5 c a,
rw h4 at h8,
let h9 := h8.2,
have h10 : R a' b c,
  unfold R,
  rw h3,
  exact eqd.trans h9.symm.flip (eqd.trans h_1 h7.flip),
exact h5 (eight6 h h10 h8.1)
end

theorem eight8 {a b : point} : R a b a → a = b :=
begin
intro h,
exact eight7 (eight5 b a).symm h 
end

theorem eight9 {a b c : point} : R a b c → col a b c → a = b ∨ c = b :=
begin
intros h h1,
cases em (a = b),
  simp *,
right,
let h2 := eight3 h h_1 (four11 h1).2.1,
exact eight8 h2
end

theorem eight10 {a b c a' b' c' : point} : R a b c → cong a b c a' b' c' → R a' b' c' :=
begin
intros h h1,
cases em (b = c),
  rw h_1 at *,
  have h2 : b' = c',
    exact id_eqd b' c' c h1.2.1.symm,
  rw h2,
  exact eight5 a' c',
unfold R at *,
generalize h2 : S b c = d,
generalize h3 : S b' c' = d',
let h4 := seven5 b c,
let h5 := seven5 b' c',
rw h2 at *,
rw h3 at *,
have h6 : afs c b d a c' b' d' a',
  repeat {split},
    exact h4.1,
    exact h5.1,
    exact h1.2.1.flip,
    exact eqd.trans h4.2.symm (eqd.trans h1.2.1 h5.2),
    exact h1.2.2.flip,
  exact h1.1.flip,
let h7 := afive_seg h6 (ne.symm h_1),
exact eqd.trans h1.2.2.symm (eqd.trans h h7.flip)
end

def perpx (x : point) (A A' : set point) : Prop := line A ∧ line A' ∧ x ∈ A ∧ x ∈ A' ∧
∀ u v, u ∈ A → v ∈ A' → R u x v

def perpx1 (x a b : point) (A : set point) : Prop := a ≠ b ∧ perpx x A (l a b)

def perpx2 (x a b c d : point) : Prop := a ≠ b ∧ c ≠ d ∧ perpx x (l a b) (l c d)

def perp (A A' : set point) : Prop := ∃ x, perpx x A A'

def perp1 (a b : point) (A : set point) : Prop := a ≠ b ∧ perp A (l a b)

def perp2 (a b c d : point) : Prop := a ≠ b ∧ c ≠ d ∧ perp (l a b) (l c d)

notation A ⊥ B  := perp A B

notation A ⊥ B % x  := perpx x A B

end Euclidean_plane

/-
reminder:
∃ at most 1,
setoid,
-/
