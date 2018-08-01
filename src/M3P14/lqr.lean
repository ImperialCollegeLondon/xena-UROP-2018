import tactic.ring 
import data.nat.prime
import data.nat.modeq data.int.modeq
import analysis.real
import tactic.norm_num
import algebra.group_power
import M3P14.order
import data.nat.prime
import chris_hughes_various.zmod
import M3P14.sheet1
import tactic.ring
import logic.basic
import data.int.basic


open nat 

definition quadratic_res (a n : ℤ) := ∃ x : ℕ, a ≡ x^2 [ZMOD n]

attribute [instance, priority 0] classical.prop_decidable
noncomputable definition legendre_sym {p : ℕ} (a : ℤ) (H1 : prime p ∧ p ≠ 2) : ℤ := 
if quadratic_res a p ∧ ¬ ((p : ℤ) ∣ a) then 1 else 
if ¬ quadratic_res a p then -1 
else 0

theorem law_of_quadratic_reciprocity {p q : ℕ} (hp : prime p ∧ p ≠ 2) (hq : prime q ∧ q ≠ 2) : (legendre_sym p hq)*(legendre_sym q hp) = (-1)^(((p-1)/2)*((q-1)/2)) := sorry 

theorem law_of_quadratic_reciprocity' {p q : ℕ} (hp : prime p ∧ p ≠ 2) (hq : prime q ∧ q ≠ 2) : (legendre_sym p hq) = (legendre_sym q hp) * (-1)^(((p-1)/2)*((q-1)/2)):= sorry 

theorem legendre_sym_mul {p : ℕ} (a b : ℤ) (hp : prime p ∧ p ≠ 2) : legendre_sym (a*b) hp = (legendre_sym a hp)*(legendre_sym b hp) := sorry

theorem legendre_sym_refl {p : ℕ} (a b : ℤ) (hp : prime p ∧ p ≠ 2) :  (a ≡ b [ZMOD p] → legendre_sym a hp = legendre_sym b hp) := sorry

theorem LQR_supplementary_1 {p : ℕ} (hp : prime p ∧ p ≠ 2) : legendre_sym (-1:ℤ) hp = (-1:ℤ)^((p-1)/2) := 
begin
have h1 : ¬ ((p:ℤ)∣(-1:ℤ)), 
{
  intro h, 
  have h2 : ((p:ℤ)∣1), from int.dvd_nat_abs.2 h,
  have h3 : p ≥ 0, sorry,
  --have : p = 1, from eq_one_of_dvd_one h2 --(prime.pred_pos hp.1) h2 
  sorry,
},
--apply euler_criterion p (-1) hp h1
sorry,
end

theorem LQR_supplementary_2 {p : ℕ} (hp : prime p ∧ p ≠ 2) : legendre_sym 2 hp = (-1:ℤ)^((p^2-1)/8) := sorry 

theorem legendre_one {p : ℕ} (hp : prime p ∧ p ≠ 2) : legendre_sym 1 hp = 1 := sorry

theorem legendre_neg_one {p : ℕ} (hp : prime p ∧ p ≠ 2) : legendre_sym (-1) hp = (-1)^((p-1)/2) := sorry

theorem pow_two_eq_mul_self (x : ℕ) : x^2 = x * x := begin show 1*x*x=x*x,rw one_mul end

theorem factorization_x_square_minus_one(x : ℕ) : x^2-1 = (x+1)*(x-1):= begin
  rw pow_two_eq_mul_self,
  cases x with t,
  norm_num,
  show (t+1) * (t+1) - 1 = (succ t + 1) * t,
  ring,
end

<<<<<<< HEAD
--theorem num_of_quad_res {p : ℕ} (hp : prime p ∧ p ≠ 2) : ∃ (A : set ℕ) [finset A], ∀ x : [1, (p-1)], (legendre_sym x hp = 1 ↔ x ∈ A) ∧ finset.card A = (p-1)/2

@[simp] lemma int.cast_pow {α : Type*} [ring α] (a : ℤ) (n : ℕ): ((a ^ n : ℤ) : α) = a ^ n :=
by induction n; simp [*, _root_.pow_succ]


@[simp] lemma nat.cast_pow {α : Type*} [semiring α] (a : nat) (n : ℕ): 
((a ^ n : ℕ ) : α) = a ^ n :=
by induction n; simp [*, _root_.pow_succ, nat.pow_succ, mul_comm]



lemma euler_c_1 (a p : ℕ) (hp : prime p ∧ p ≠ 2) (ha : ¬ p ∣ a) : quadratic_res a p → a^((p-1)/2) ≡ 1 [ZMOD p] := 
=======
@[simp] theorem int.cast_pow {α : Type*} [ring α] (a : ℤ) (n : ℕ): ((a ^ n : ℤ) : α) = a ^ n :=
by induction n; simp [*, _root_.pow_succ]


theorem euler_c_1 (a p : ℕ) (hp : prime p ∧ p ≠ 2) (ha : ¬ p ∣ a) : quadratic_res a p → a^((p-1)/2)-1 ≡ 0 [ZMOD p] := 
>>>>>>> 92b9d48860f0f68de78ccdd3c103335d9b55d5c8
begin
intro Hqr,
cases Hqr with x hx,
haveI : prime p := hp.1,
rw ← zmod.eq_iff_modeq_int,
rw ← zmod.eq_iff_modeq_int at hx,
have q: 2 ∣ (p-1):=
begin
  cases nat.mod_two_eq_zero_or_one p,
  have : p % 2 ≡ p [MOD 2], from nat.modeq.mod_modeq p 2,
  have : 0 ≡ p [MOD 2], from eq.subst h this,
  have : p ≡ 0 [MOD 2], from modeq.symm this,
  rw ← nat.modeq.modeq_zero_iff,
  exfalso,
  have h1 := hp.1.2 2 (nat.modeq.modeq_zero_iff.1 this),
  cases h1 with h3 h4,
  have h2: 2 ≠ 1, by norm_num,
  exact h2 h3,
  exact hp.2.symm h4,
  rw ← nat.mod_add_div p 2,
  rw h, rw nat.add_sub_cancel_left,
  simp,
end,
<<<<<<< HEAD
rw int.cast_pow, rw hx, rw int.cast_pow, rw ← pow_mul, rw nat.mul_div_cancel' q,
have h1 : x^(p-1) ≡ 1 [MOD p], from fermat_little_theorem_extension x p hp.1,
have h2 : ↑(x^(p-1)) ≡ ↑1 [ZMOD ↑p], from (int.modeq.coe_nat_modeq_iff (x^(p-1)) 1 p).2 h1,
have h3 : ↑(x^(p-1)) = ↑1, from zmod.eq_iff_modeq_int.2 h2,
rw ← int.cast_pow,
suffices h4 : x^(p-1) = ↑x^(p-1), rw h4 at h3, 
simpa [nat.cast_pow]using h3,
simp,
=======
rw int.cast_sub, rw int.cast_pow, rw hx, rw int.cast_pow, rw ← pow_mul, rw nat.mul_div_cancel' q,
--have hx_eq: ↑a = ↑(x^2) , from ← zmod.eq_iff_modeq_int,
--↑a Mod p = ↑x^2 MOD p
--have ↑a ^ ((p - 1) / 2) - 1 = x ^ (p-1), from 
--{
--  calc 
--  ↑a ^ ((p - 1) / 2) - 1 = (x ^ 2) ^ ((p - 1) / 2) - 1  : by rw eq.subst 
--},

>>>>>>> 92b9d48860f0f68de78ccdd3c103335d9b55d5c8
end


lemma euler_c_2 (a p : ℕ) (hp : prime p ∧ p ≠ 2) (ha : ¬ p ∣ a) : ¬ (quadratic_res a p) → a^((p-1)/2) ≡ -1 [ZMOD p] := sorry


theorem euler_criterion (p : ℕ) (a : ℕ) (hp : prime p ∧ p ≠ 2) (ha : ¬ p ∣ a) :
  (a^((p - 1) / 2) : ℤ) ≡ legendre_sym a hp [ZMOD p] := 
begin 
  have h1 : a^(p-1) ≡ 1 [MOD p], from fermat_little_theorem_extension a p hp.left,
  have h2 : ↑(a ^ (p - 1)) ≡ ↑1 [ZMOD ↑p], from (int.modeq.coe_nat_modeq_iff (a^(p-1)) 1 p).mpr h1,
  have h3 : ↑1 ≡ ↑1 [ZMOD p], from int.modeq.refl 1,
  have h4 : ((a ^ (p - 1)) : ℕ) - 1 ≡ 0 [ZMOD p], from int.modeq.modeq_sub h2 h3,
  have h5 : (a ^ ((p - 1)/2))^2-1 = (a^((p-1)/2)+1)*(a^((p-1)/2)-1), from factorization_x_square_minus_one (a^((p-1)/2)),
  unfold legendre_sym,
  split_ifs,
  exact euler_c_1 a p hp ha h.1,
  exfalso,
  have h7 : ¬quadratic_res ↑a ↑p, from not_and'.1 h (show ¬↑p ∣ ↑a, from (not_iff_not.2 int.coe_nat_dvd).2 ha),
  from absurd h_1 h7,
  exact euler_c_2 a p hp ha h_1,
end



--Let p be an odd prime. Then there are exactly (p - 1) /2 quadratic residues modulo p and exactly (p - 1) /2 nonresidues modulo p. 
--theorem quad_res_sol {p : ℕ} (hp : prime p) : 

theorem minus_one_quad_res_of_p {p : ℕ} (hp : prime p ∧ p ≠ 2) : (p ≡ 1 [MOD 4] ↔ legendre_sym (-1 : ℤ) hp = 1) ∧ (p ≡ 3 [MOD 4] ↔ legendre_sym (-1 : ℤ) hp = (-1 : ℤ)) := sorry

theorem quad_res_two (n : ℕ) : n % 8 = 1 ∨ n % 8 = 7 → ((n ^ 2 - 1) / 8 % 2 = 0) :=
begin
  intro H,
  have H2 := nat.mod_add_div n 8,
  cases H,
  { rw H at H2,
    rw ←H2,
    rw ←nat.dvd_iff_mod_eq_zero,
    suffices : ∀ t, 2 ∣ ((1 + 8 * t) ^ 2 - 1) / 8,
      exact this (n/8),
    intro t,
    existsi t+4*t*t,
    show (1 * (1 + 8 * t) * (1 + 8 * t) - 1) / 8 = 2 * (t + 4 * t * t),
    rw (show 1 * (1 + 8 * t) * (1 + 8 * t) = 8 * (2 * t + 8 * t * t) + 1, by ring),
    rw nat.add_sub_cancel,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  },
  { rw H at H2,
    rw ←H2,
    rw ←nat.dvd_iff_mod_eq_zero,
    suffices : ∀ t, 2 ∣ ((7 + 8 * t) ^ 2 - 1) / 8,
      exact this (n/8),
    intro t,
    existsi 3+7*t+4*t*t,
    show (1 * (7 + 8 * t) * (7 + 8 * t) - 1) / 8 = 2 * (3 + 7 * t + 4 * t * t),
    rw (show 1 * (7 + 8 * t) * (7 + 8 * t) = 8 * (6 + 14 * t + 8 * t * t) + 1, by ring),
    rw nat.add_sub_cancel,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  }
end 

theorem quad_nonres_two (n : ℕ) : n % 8 = 3 ∨ n % 8 = 5 → ((n ^ 2 - 1) / 8 % 2 = 1) :=
begin
  intro H,
  have H2 := nat.mod_add_div n 8,
  cases H,
  { rw H at H2,
    rw ←H2,
    suffices : ∀ t : ℕ, ((3 + 8 * t) ^ 2 - 1) / 8 % 2 = 1,
      exact this (n/8),
    intro t,
    have H3 : (1 + 2 * (4*t^2 + 3*t)) % 2 = 1,
      rw nat.add_mul_mod_self_left,exact dec_trivial,
    suffices : ((3 + 8 * t) ^ 2 - 1) / 8 = (1 + 2 * (4 * t ^ 2 + 3 * t)),
      rwa this,
    suffices : ((3 + 8 * t) ^ 2 - 1) = 8 * (1 + 2 * (4 * t ^ 2 + 3 * t)),
      rw this,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  },
  { rw H at H2,
    rw ←H2,
    suffices : ∀ t : ℕ, ((5 + 8 * t) ^ 2 - 1) / 8 % 2 = 1,
      exact this (n/8),
    intro t,
    have H3 : (1 + 2 * (4*t^2 + 5*t + 1)) % 2 = 1,
      rw nat.add_mul_mod_self_left,exact dec_trivial,
    suffices : ((5 + 8 * t) ^ 2 - 1) / 8 = (1 + 2 * (4 * t ^ 2 + 5 * t + 1)),
      rwa this,
    suffices : ((5 + 8 * t) ^ 2 - 1) = 8 * (1 + 2 * (4 * t ^ 2 + 5 * t + 1)),
      rw this,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  }
end 