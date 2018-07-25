import data.set
import Euclid.tarski_1
open classical set
namespace Euclidean_plane
variables {point : Type} [Euclidean_plane point]

theorem six9 {a b p : point} : b ∈ ray p a → ray p a = ray p b :=
begin
intro h,
ext,
apply iff.intro,
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

def l (a b : point) : set point := {x | col a b x}

def line (k : set point) : Prop := ∃ a b, a ≠ b ∧ k = l a b

theorem six15 {p q r : point} : p ≠ q → p ≠ r → B q p r → l p q = ray p q ∪ {p} ∪ ray p r :=
begin
intros h h1 h2,
ext,
apply iff.intro,
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
    simp at *,
    exact h3,
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
apply iff.intro,
  intro h3,
  exact five4 h h2 h3,
intro h3,
have : col p r q,
  exact (four11 h2).1,
exact five4 h1 this h3
end

end Euclidean_plane