import data.int.basic
import data.int.modeq
import data.int.order
import algebra.group_power
import tactic.ring
import chris_hughes_various.zmod
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
noncomputable definition legendre_sym {p : ℤ} (a : ℤ) (H1 : prime_int p ∧ p ≠ 2) : ℤ := 
if quadratic_res a p ∧ ¬ ((p : ℤ) ∣ a) then 1 else 
if ¬ quadratic_res a p then -1 
else 0

-- lemmas

lemma legendre_strong_mul {p : ℤ} (a b : ℤ) (H1 : prime_int p ∧ p ≠ 2) : legendre_sym (a*b) H1 = (legendre_sym a H1) * (legendre_sym b H1)  := sorry

lemma if_cong_legendre_eq {p : ℤ} (a b : ℤ) (H1 : prime_int p ∧ p ≠ 2) : a % p = b → legendre_sym a H1 = legendre_sym b H1 := sorry

lemma euler_criterion {p : ℤ} (a : ℤ) (H1 : prime_int p ∧ p ≠ 2) : legendre_sym a H1 = a^(int.nat_abs p-1) % p := sorry

theorem legendre_sym_one_implies_quadratic_res {p : ℤ} (a : ℤ)(H1 : prime_int p ∧ p ≠ 2): legendre_sym a H1 = 1 → quadratic_res a p :=
begin 
intro h,
unfold legendre_sym at h,
split_ifs at h, 
exact h_1.1,
exfalso,
revert h, norm_num,
revert h, norm_num,
end


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

theorem one_mod_four_prime (p : ℤ)(h : prime_int p ∧ p ≠ 2) : p ^ 2 ≡  1 [ZMOD 4] := sorry 

theorem fermat_descent (p : ℤ)(h : prime_int p ∧ p ≠ 2) : ∃ a b r : ℤ, (a ^ 2 + b ^ 2 = p * r) ∧ (1 < r) ∧ (r < p) → ∃ x y r' : ℤ, (1 ≤ r') ∧ (r'< r) ∧ (x ^ 2 + y ^ 2 = p * r') := 
begin
sorry 
end 

theorem fermat_two_square (p : ℤ)(h : prime_int p ∧ p ≠ 2)(H: p ≥ 0) : p ≡ 1 [ZMOD 4] → is_sum_of_two_squares (int.nat_abs p) := 
begin
intro hpp, 
have b1 := (minus_one_quad_res_of_p h).1.1,
have b2 := b1 hpp,
have b3 := legendre_sym_one_implies_quadratic_res (-1) h b2,
unfold quadratic_res at b3,
rcases b3 with x,
let y := x % ↑(int.nat_abs p),
have b3_hh : -1 ≡ y ^ 2 [ZMOD ↑(int.nat_abs p)], 
begin 
haveI : pos_nat p.nat_abs := sorry,
rw ← zmod.eq_iff_modeq_int,
rw ← zmod.eq_iff_modeq_int at b3_h,
have : x ≡ y [ZMOD ↑(p.nat_abs)], 
exact (int.mod_mod x p.nat_abs).symm,
rw ← zmod.eq_iff_modeq_int at this,
rw int.cast_pow at b3_h,
rw int.cast_pow,
exact eq.subst this b3_h,
end,
have b4 : 1 ≡ 1 [ZMOD ↑(int.nat_abs p)], by refl,
have b5 := int.modeq.modeq_add b3_hh b4, 
have b6 : (-1 :ℤ) + 1 = 0, by simp,
rw b6 at b5, 
have b7 := int.modeq.symm b5,
rw int.nat_abs_of_nonneg at b7,
have b8:= int.modeq.modeq_zero_iff.1 b7,
have b9 := exists_eq_mul_right_of_dvd b8,
rcases b9 with r,
have c : (1 ≤ r) ∧ (r < p), 
begin
split, 
have c1 : 0 < y ^ 2 + 1, 
{ 
    rw int.lt_add_one_iff,
    exact pow_two_nonneg y,
},
have c2 : p * r > 0, from eq.subst b9_h c1,  
have c3 := pos_of_mul_pos_left c2 H, exact c3,
have c4 : y ≥ 0 ∧ y ≤ p - 1, 
split, 
have c5 : x % ↑(int.nat_abs p) ≥ 0, from int.mod_nonneg _ _, 

--exact int.mod_nonneg x int.nat_abs p,
--have c5 : p * r ≤ (p - 1) ^ 2 + 1 , from eq.subst b9_h begin end,
sorry, 
end,   
sorry,
exact H,
end 
#check mod_lt
#check int.mod_nonneg

--inductive less_than_or_equal (a : ℤ) : ℤ → Prop
--| refl : less_than_or_equal a
--| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

--def le_refl : ∀ a : ℤ, a ≤ a :=
--less_than_or_equal.refl


--lemma le_succ (n:ℤ) : n ≤ succ n :=
--less_than_or_equal.step (int.le_refl n)


--theorem le_of_succ_le {n m : ℤ} (h : succ n ≤ m) : n ≤ m := 
--int.le_trans (le_succ n) h