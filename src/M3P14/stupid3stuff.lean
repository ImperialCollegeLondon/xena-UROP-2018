import data.int.modeq
import chris_hughes_various.zmod

namespace int
theorem eq_self_mod {n : ℤ} (x : ℤ) : x ≡ (x % n) [ZMOD n] :=
begin
  show x % n = (x % n) % n,
  rw int.mod_mod,
end

end int 
open int

theorem mod_3_lt_3 (x : ℤ) : 0 ≤ x % 3 ∧ x % 3 < 3 :=
begin
  split,
    exact mod_nonneg x (dec_trivial),
  exact @mod_lt x 3 (dec_trivial)
end

theorem cheat (d : ℤ) : 0 ≤ d ∧ d < 3 → d = 0 ∨ d = 1 ∨ d = 2 := 
begin
  cases d with d1 d2,
  { rintro ⟨h1,h2⟩,
    cases d1,
    left,refl,
    cases d1,
    right,left,refl,
    cases d1,
    right,right,refl,
    revert h2,exact dec_trivial,
  },
  intro H,
  cases H with H1 H2,
  exfalso,
  revert H1,
  exact dec_trivial,
end

theorem mod_lt_3 (x : ℤ) : x ≡ 0 [ZMOD 3] ∨ x ≡ 1 [ZMOD 3] ∨ x ≡ 2 [ZMOD 3] :=
begin
  let d := x % 3,
  have H : x ≡ d [ZMOD 3],
    exact eq_self_mod x,
  have H2 : 0 ≤ d ∧ d < 3,
    exact mod_3_lt_3 x,
  have H3 : d = 0 ∨ d = 1 ∨ d = 2,
    revert H2,
    exact cheat d,
  cases H3 with H0 H12,
  left,convert H,exact H0.symm,
  cases H12 with H1 H2',
  right,left,convert H,exact H1.symm,
  right,right,convert H,exact H2'.symm,
end

example (x : ℤ) : x ^ 2 ≡ 1 [ZMOD 3] ∨ x ^ 2 ≡ 0 [ZMOD 3] := begin
sorry,
end
