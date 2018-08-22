import tactic.ring 
import data.nat.prime
import data.nat.modeq data.int.modeq
import analysis.real
import tactic.norm_num
import algebra.group_power
import M3P14.order
import chris_hughes_various.zmod
import M3P14.Problem_sheets.sheet1
import tactic.ring
import logic.basic
import data.int.basic

open nat 


definition prime_int (p : ℤ) := prime(int.nat_abs p) 
theorem prime_int_to_nat {p : ℤ} (h : prime_int p) : prime (int.nat_abs p) :=
begin
exact (show prime(int.nat_abs p), from h),
end

definition quadratic_res (a n : ℤ) := ∃ x : ℤ, a ≡ x^2 [ZMOD (int.nat_abs n)]
--definition quadratic_res' (p : ℤ) (hp : prime_int p ∧ p ≠ 2) (a n : zmod p) := ∃ x : ℕ, a ≡ x^2 [ZMOD n]

attribute [instance, priority 0] classical.prop_decidable
noncomputable definition legendre_sym {p : ℤ} (a : ℤ) (H1 : prime_int p ∧ (int.nat_abs p) ≠ 2) : ℤ := 
if quadratic_res a p ∧ ¬ (a ≡ 0 [ZMOD p]) then 1 else 
if ¬ quadratic_res a p then -1 
else 0

theorem law_of_quadratic_reciprocity {p q : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) (hq : prime_int q ∧ (int.nat_abs q) ≠ 2) : (legendre_sym p hq)*(legendre_sym q hp) = (-1)^(int.nat_abs(((p-1)/2)*((q-1)/2))) := sorry 

theorem law_of_quadratic_reciprocity' {p q : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) (hq : prime_int q ∧ (int.nat_abs q) ≠ 2) : (legendre_sym p hq) = (legendre_sym q hp) * (-1)^(int.nat_abs(((p-1)/2)*((q-1)/2))):= sorry 

theorem legendre_sym_mul {p : ℤ} (a b : ℤ) (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) : legendre_sym (a*b) hp = (legendre_sym a hp)*(legendre_sym b hp) := sorry

theorem legendre_sym_refl {p : ℤ} (a b : ℤ) (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) :  (a ≡ b [ZMOD p] → legendre_sym a hp = legendre_sym b hp) := sorry

theorem LQR_supplementary_2 {p : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) : legendre_sym 2 hp = (-1:ℤ)^(int.nat_abs((p^2-1)/8)) := sorry 

theorem legendre_one {p : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) : legendre_sym 1 hp = 1 := sorry

theorem legendre_neg_one {p : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) : legendre_sym (-1) hp = (-1)^(int.nat_abs((p-1)/2)) := sorry

theorem pow_two_eq_mul_self (x : ℕ) : x^2 = x * x := begin show 1*x*x=x*x,rw one_mul end

theorem factorization_x_square_minus_one(x : ℕ) : x^2-1 = (x+1)*(x-1):= begin
  rw pow_two_eq_mul_self,
  cases x with t,
  norm_num,
  show (t+1) * (t+1) - 1 = (succ t + 1) * t,
  ring,
end

--theorem num_of_quad_res {p : ℕ} (hp : prime_int p ∧ p ≠ 2) : ∃ (A : set ℕ) [finset A], ∀ x : [1, (p-1)], (legendre_sym x hp = 1 ↔ x ∈ A) ∧ finset.card A = (p-1)/2

/- ALREADY DECLARED
#check int.cast_pow
@[simp] lemma int.cast_pow {α : Type*} [ring α] (a : ℤ) (n : ℕ): ((a ^ n : ℤ) : α) = a ^ n :=
by induction n; simp [*, _root_.pow_succ]


@[simp] lemma nat.cast_pow {α : Type*} [semiring α] (a : nat) (n : ℕ): 
((a ^ n : ℕ ) : α) = a ^ n :=
by induction n; simp [*, _root_.pow_succ, nat.pow_succ, mul_comm]

lemma int.mod_two_eq_zero_or_one (n : ℤ): n % 2 = 0 ∨ n % 2 = 1 := 
have h: n % 2 < 2 := abs_of_nonneg (show (2 : ℤ) ≥ 0, from dec_trivial) ▸
int.mod_lt _ dec_trivial, 
have h1 : n % 2 ≥ 0 := int.mod_nonneg _ dec_trivial, 
match (n % 2), h, h1 with 
| (0 : ℕ) := λ _ _, or.inl rfl
| (1 : ℕ) := λ _ _, or.inr rfl
| (k+2 : ℕ) := λ h _, absurd h dec_trivial
|(-[1+ a]) := λ _ h1, absurd h1 dec_trivial 
end
-/

lemma int.modeq.mod_modeq : ∀ (a n : ℤ), a % n ≡ a [ZMOD (int.nat_abs n)] := sorry 

lemma int.add_sub_cancel_left : ∀ (n m : ℤ), n + m - n = m := sorry

lemma yet_to_prove (x : ℤ) (p : ℤ) (hp : prime_int p ∧ int.nat_abs p ≠ 2) : (x ^ int.nat_abs (p - 1)) = (int.nat_abs x) ^ (int.nat_abs p - 1)  := sorry

lemma odd_prime_int_is_odd {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : p % 2 = 1 := 
begin
unfold prime_int at hp,
sorry,
end

variable p : ℤ
variable hp : prime_int p ∧ int.nat_abs p ≠ 2
#check hp.1


theorem euler_c_1 (a p : ℤ) (hp : prime_int p ∧ int.nat_abs p ≠ 2) (ha : ¬ p ∣ a) : quadratic_res a p → a^int.nat_abs((p-1)/2) ≡ 1 [ZMOD (int.nat_abs p)] := 
begin
intro Hqr,
cases Hqr with x hx,
haveI : prime_int p := hp.1,
haveI : pos_nat(int.nat_abs p) := sorry,
rw ← zmod.eq_iff_modeq_int,
rw ← zmod.eq_iff_modeq_int at hx,
have q: 2 ∣ int.nat_abs(p-1):=
begin
  cases nat.mod_two_eq_zero_or_one (int.nat_abs p),
  have : (int.nat_abs p) % 2 ≡ int.nat_abs p [MOD 2], from nat.modeq.mod_modeq (int.nat_abs p) 2,
  have : 0 ≡ int.nat_abs p [MOD 2], from eq.subst h this,
  have : int.nat_abs p ≡ 0 [MOD 2], from nat.modeq.symm this,
  rw ← nat.modeq.modeq_zero_iff,
  exfalso,
  have h1 := hp.1.2 _ (nat.modeq.modeq_zero_iff.1 this),
  cases h1 with h3 h4,
  have h2: 2 ≠ 1, by norm_num,
  exact h2 h3,
  exact hp.2.symm h4,
  rw ← int.coe_nat_dvd,
  rw int.dvd_nat_abs,
  rw ← int.mod_add_div p 2,
  have : p % 2 = 1, from odd_prime_int_is_odd hp,
  rw this, rw int.add_sub_cancel_left,
  have r: 2 ≠ 0, by norm_num,
  exact dvd_mul_right _ _,
end,
have h5 : int.nat_abs ((p-1)/2) = (int.nat_abs (p-1))/2, sorry,
rw int.cast_pow, rw hx, rw int.cast_pow, rw ← pow_mul, rw h5, rw nat.mul_div_cancel' q,
have h : prime (int.nat_abs p),{unfold prime_int at _inst; exact _inst},
have h1 : (int.nat_abs x)^((int.nat_abs p) -1) ≡ 1 [MOD (int.nat_abs p)], from fermat_little_theorem_extension (int.nat_abs x) (int.nat_abs p) h,
have h2 : ↑(int.nat_abs x ^ (int.nat_abs p - 1)) ≡ ↑1 [ZMOD ↑(int.nat_abs p)], from (int.modeq.coe_nat_modeq_iff ((int.nat_abs x)^((int.nat_abs p) -1)) 1 (int.nat_abs p)).2 h1,
have h3 : ↑(↑(int.nat_abs x ^ (int.nat_abs p - 1))) = ↑1, from zmod.eq_iff_modeq_int.2 h2,
rw ← int.cast_pow,
simp at h3,
rw yet_to_prove _ _ hp,
simp [h3],
end


lemma euler_c_2 (a p : ℤ) (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) (ha : ¬ p ∣ a) : ¬ (quadratic_res a p) → a^int.nat_abs((p-1)/2) ≡ -1 [ZMOD (int.nat_abs p)] := sorry


theorem euler_criterion (p : ℤ) (a : ℤ) (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) (ha : ¬ p ∣ a) :
  a^int.nat_abs((p - 1) / 2) ≡ legendre_sym a hp [ZMOD (int.nat_abs p)] := 
begin 
  unfold legendre_sym,
  split_ifs,
  exact euler_c_1 a p hp ha h.1,
  exfalso,
  have h8 : ¬quadratic_res a p, from not_and'.1 h (show ¬p ∣ a, from ha),
  from absurd h_1 h8,
  exact euler_c_2 a p hp ha h_1,
end

theorem not_prime_int_one : ¬(prime_int 1) := 
by unfold prime_int; exact dec_trivial

theorem LQR_supplementary_1 {p : ℤ} (hp : prime_int p ∧ (int.nat_abs p) ≠ 2) (hpp : p ≥ 0): legendre_sym (-1:ℤ) hp = (-1:ℤ)^int.nat_abs((p-1)/2) := 
begin 
have h1 : ¬ ((p:ℤ)∣(-1:ℤ)), 
{
  intro h, 
  have h2 : p = 1, from int.eq_one_of_dvd_one hpp (show ((p:ℤ)∣1), from int.dvd_nat_abs.2 h),
  exact not_prime_int_one (show prime_int 1, from eq.subst h2 hp.1),
},
have h6 : (-1)^int.nat_abs((p - 1) / 2) ≡ legendre_sym (-1) hp [ZMOD (int.nat_abs p)] , from euler_criterion p (-1) hp h1,
haveI : pos_nat(int.nat_abs p) := sorry,
--exact ((int.coe_nat_eq_coe_nat_iff ((-1) ^ int.nat_abs ((p - 1) / 2)) (legendre_sym (-1) hp)).2 eq.symm(zmod.eq_iff_modeq_int.2 h6)),
sorry,
end 
#check int.coe_nat_eq_coe_nat_iff
--theorem Jason_and_partly_Guy_did_it {p : ℕ} (hp : prime_int p ∧ p ≠ 2) : ∃ A : finset (zmod p), ∀ a : zmod p, (quadratic_res' a p ↔ a ∈ A) ∧ finset.card A = (p-1)/2 := sorry

theorem Guy_suggested_this_but_i_am_not_sure {p : ℕ} (hp : prime_int p ∧ p ≠ 2) : ∃ A : finset ℕ, ∀ a : ℕ, (¬quadratic_res a p ↔ a ∈ A) ∧ finset.card A = (p-1)/2 := sorry
--Let p be an odd prime_int. Then there are exactly (p - 1) /2 quadratic residues modulo p and exactly (p - 1) /2 nonresidues modulo p. 
--theorem quad_res_sol {p : ℕ} (hp : prime_int p) : 

theorem minus_one_quad_res_of_p {p : ℕ} (hp : prime_int p ∧ p ≠ 2) : (p ≡ 1 [MOD 4] ↔ legendre_sym (-1 : ℤ) hp = 1) ∧ (p ≡ 3 [MOD 4] ↔ legendre_sym (-1 : ℤ) hp = (-1 : ℤ)) := sorry

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