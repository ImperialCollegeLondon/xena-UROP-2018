import data.int.basic
import data.int.modeq
import data.int.order
import algebra.group_power
import tactic.ring
open nat 

--#check int.le
--theorem l_to_le {a b : ℤ} (hab : a < b) : a ≤ b := begin
--unfold has_le.le,
--unfold int.le,
--have h1 : b < b+1, by lt_succ_self b, 
--end

definition prime_int (p : ℤ) := nat.prime(int.nat_abs p) 
theorem prime_int_to_nat {p : ℤ} (h : prime_int p) : prime (int.nat_abs p) := sorry

definition quadratic_res (a n : ℤ) := ∃ x : ℤ, a ≡ x^2 [ZMOD (int.nat_abs n)]
--definition quadratic_res' (p : ℤ) (hp : prime_int_int p ∧ p ≠ 2) (a n : zmod p) := ∃ x : ℕ, a ≡ x^2 [ZMOD n]

attribute [instance, priority 0] classical.prop_decidable
noncomputable definition legendre_sym {p : ℤ} (a : ℤ) (H1 : prime_int p ∧ p≠ 2) : ℤ := 
if quadratic_res a p ∧ ¬ ((p : ℤ) ∣ a) then 1 else 
if ¬ quadratic_res a p then -1 
else 0

theorem minus_one_quad_res_of_p {p : ℤ} (hp : prime_int p ∧ p ≠ 2) : (p ≡ 1 [ZMOD 4] ↔ (legendre_sym (-1: ℤ) hp) = 1) ∧ (p ≡ 3 [ZMOD 4] ↔ legendre_sym (-1 : ℤ) hp = (-1 : ℤ)) := sorry


definition is_sum_of_two_squares (n : ℕ) := ∃ x y : ℤ, (n : ℤ) =  x ^ 2 + y ^ 2


theorem is_sum_of_two_squares_mul (m n : ℕ) : is_sum_of_two_squares m ∧ is_sum_of_two_squares n → is_sum_of_two_squares (m * n) := 
begin
intro h,
unfold is_sum_of_two_squares,
unfold is_sum_of_two_squares at h, 
rcases h with ⟨⟨a, b, hab⟩, ⟨c, d, hcd⟩⟩,
existsi [a * c - b * d, a * d + b * c],
rw int.coe_nat_mul, rw hab, rw hcd, 
ring,
end 

theorem one_mod_four_prime (p : ℤ)(h : prime_int p) : p ^ 2 ≡  1 [ZMOD 4] := sorry 

theorem fermat_descent (p : ℤ)(h : prime_int p) : ∃ a b r : ℤ, (a ^ 2 + b ^ 2 = p * r) ∧ (1 < r) ∧ (r < p) → ∃ x y r' : ℤ, (1 ≤ r') ∧ (r'< r) ∧ (x ^ 2 + y ^ 2 = p * r') := 
begin
sorry 
end 

theorem fermat_two_square (p : ℤ)(h : prime_int p) : p ≡ 1 [ZMOD 4] → is_sum_of_two_squares (int.nat_abs p) := 
begin
intro hpp, 
have hp : prime_int p ∧ p ≠ 2, 
begin 
split, 
exact h, 
by_contradiction,
sorry 
end, 
sorry 
end   

 

--inductive less_than_or_equal (a : ℤ) : ℤ → Prop
--| refl : less_than_or_equal a
--| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

--def le_refl : ∀ a : ℤ, a ≤ a :=
--less_than_or_equal.refl


--lemma le_succ (n:ℤ) : n ≤ succ n :=
--less_than_or_equal.step (int.le_refl n)


--theorem le_of_succ_le {n m : ℤ} (h : succ n ≤ m) : n ≤ m := 
--int.le_trans (le_succ n) h