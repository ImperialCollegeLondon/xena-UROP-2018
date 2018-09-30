import M3P14.lqr
import data.list.basic
import data.padics.padic_norm


open int list


lemma identity (c d n x y : ℤ) : (c^2 + n*d^2)*(x^2 + n*y^2) = (x*c - n*d*y)^2 + n*(c*y + d*x)^2 := by ring

lemma nonneg_int {a x y n : ℤ} (hn : 0 < n) : a = x^2 + n*y^2 → 0 ≤ a := begin
intro h, rw h,
have := add_le_add' (mul_self_nonneg x) ((mul_le_mul_left hn).2 (mul_self_nonneg y)),
ring at this, exact this,
end

lemma pow_ne_zero' {k : ℕ} {a : ℤ} (h : a ≠ 0) : a ^ k ≠ 0 := begin
induction k with k h0,
simp, 
rw [pow_succ],
exact mul_ne_zero h h0,
end

lemma nat_abs_div {a b : ℤ} (h_dvd : b ∣ a) : 
nat_abs (a / b) = (nat_abs a)/(nat_abs b) := begin
cases (nat_abs_eq a) with h1 h1,
cases (nat_abs_eq b) with h2 h2,
conv {to_lhs, rw [h1, h2, ←coe_nat_div, nat_abs_of_nat]},
conv {to_lhs, rw [h1, h2, int.div_neg, nat_abs_neg, ←coe_nat_div, nat_abs_of_nat]},
rw [←nat_abs_dvd, ←dvd_nat_abs] at h_dvd,
cases (nat_abs_eq b) with h2 h2,
conv {to_lhs, rw [h1, h2, ←neg_one_mul, int.mul_div_assoc _ h_dvd, 
←coe_nat_div, neg_one_mul, nat_abs_neg, nat_abs_of_nat]},
conv {to_lhs, rw [h1, h2, int.div_neg, nat_abs_neg, ←neg_one_mul, 
int.mul_div_assoc _ h_dvd, ←coe_nat_div, neg_one_mul, 
nat_abs_neg, nat_abs_of_nat]},
end

lemma int.abs_div {a b : ℤ} (h_dvd : b ∣ a) : 
abs (a / b) = (abs a)/(abs b) := begin
rw [abs_eq_nat_abs, abs_eq_nat_abs, abs_eq_nat_abs, 
←coe_nat_div, int.coe_nat_eq_coe_nat_iff],
exact nat_abs_div h_dvd,
end

lemma int.add_div_of_dvd_right {b c : ℤ} (a : ℤ) (hb : c ∣ b) (hc : c ≠ 0) :
(a + b) / c = a / c + b / c := begin
cases hb with k hb, 
rw [hb, int.add_mul_div_left _ _ hc, int.mul_div_cancel_left _ hc], 
end

lemma int.add_div_of_dvd_left {a c : ℤ} (b : ℤ) (ha : c ∣ a) (hc : c ≠ 0) :
(a + b) / c = a / c + b / c := 
by {rw add_comm, rw int.add_div_of_dvd_right _ ha hc, simp,}

lemma neg_eq {a b : ℤ} : a = -b ↔ -a = b :=
by {split,intro,rw a_1, simp, intro, rw a_1.symm, simp}

lemma eq_nat_abs {a b :ℤ} : a = b → nat_abs a = nat_abs b := by {intro, rw a_1}

lemma prime_int_ne_zero {p : ℤ} (hp : prime_int p) : p ≠ 0 := 
begin
have := nat.prime.ne_zero hp,
norm_num, by_contradiction, rw a at this, simp at this, exact this,
end

lemma prime_int_ne_one {p : ℤ} (hp : prime_int p) : p ≠ 1 := 
begin
unfold ne, by_contradiction,
rw a at hp,
exact absurd hp nat.not_prime_one,
end

lemma prime_int_ne_neg_one {p : ℤ} (hp : prime_int p) : p ≠ (-1:ℤ) := 
begin
unfold ne, by_contradiction,
rw a at hp,
exact absurd hp nat.not_prime_one,
end

lemma prime_int_two : prime_int 2 := by {exact nat.prime_two}

lemma prime_int_three : prime_int 3 := by {exact nat.prime_three}

lemma prime_int_not_square {p : ℤ} (hp : prime_int p) :
∀ (a : ℤ), p = a^2  → false :=begin
intros a h,
have h1 :=dvd.intro (a*1) h.symm,
rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at h1,
replace h1 := hp.2 (nat_abs a) h1,
cases h1, 
have := @nat_abs_mul_self a, rw h1 at this,
ring at this, 
rw this.symm at h,
exact absurd h (prime_int_ne_one hp),
suffices : p = 1 ∨ p = (-1:ℤ),
  cases this,
  exact absurd this (prime_int_ne_one hp),
  exact absurd this (prime_int_ne_neg_one hp),
have h2 := eq_nat_abs h,
unfold pow at h2, unfold monoid.pow at h2,
rw [(nat_abs_mul a (a*1)), (mul_one a), h1] at h2,
have h4 := nat_abs_pos_of_ne_zero (prime_int_ne_zero hp),
replace h2 := eq.trans (mul_one (nat_abs p)) h2,
have := (nat.mul_left_inj h4).1 h2,
have h3:= nat_abs_eq p, rw this.symm at h3,
exact h3,
end

lemma not_two_dvd_odd_prime_int {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) : ¬ 2 ∣ p := begin
by_contradiction, 
rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at a,
cases (hp.1.2 _ a) with h h,
exact absurd h (show ¬(2:ℕ) = (1:ℕ), by norm_num),
exact absurd h.symm hp.2,
end


lemma list.prod_const_int (a : ℤ) (n : ℕ) : prod (repeat a n) = a^n := begin
induction n with n h0,
simp, rw [repeat_succ, prod_cons, h0], refl,
end

lemma list.prod_cast (X : list ℕ) : prod (↑X : list ℤ) = ↑(prod X) :=
begin
  induction X with n L HL,
    refl,
  rw prod_cons,
  rw int.coe_nat_mul,
  show prod (map coe (n :: L)) = _,
  rw map_cons,
  rw prod_cons,
  rw ←HL,
  refl,
end

lemma list.prod_ne_zero {α : Type*} [monoid α] [has_zero α]
  (h1 : ∀ x y : α, x * y = 0 → x = 0 ∨ y = 0) (h : (0 : α) ≠ 1)
  (X : list α) : (∀ x ∈ X, x ≠ (0 : α)) → prod X ≠ 0 :=
begin
  induction X with n L HL,
    intro H,
    exact h.symm,
  rw prod_cons,
  intro H,
  intro H2,
  replace H2 := h1 _ _ H2,
  cases H2,
    apply H n,simp,assumption,
  apply HL _ H2,
  intros x Hx,
  apply H x,
  simp [Hx],
end

lemma list.prod_cons_nonneg {H : list ℤ} {k : ℤ} (hk : 0 < k) (h : 0 ≤ prod (cons k H)) : 
0 ≤ prod H := begin
rw [prod_cons, mul_comm, (mul_nonneg_iff_right_nonneg_of_pos hk)] at h,
exact h,
end


lemma list.prod_nonneg_of_mem_nonneg {H : list ℤ} : (∀ k : ℤ, k ∈ H → 0 ≤ k) → 0 ≤ prod H := begin
intro h,
induction H with k H0 h0,
simp,
rw prod_cons,
have h1: (∀ (k : ℤ), k ∈ H0 → 0 ≤ k), by {intros a h1, exact h a (mem_cons_of_mem k h1)},
exact zero_le_mul (h k (mem_cons_self k H0)) (h0 h1),
end

def prime_int_factors (a : ℤ) : list ℤ := ↑(nat.factors (nat_abs a))

lemma prime_int_factors.mem (a x : ℤ) : 
x ∈ prime_int_factors a ↔ ∃ n : ℕ, n ∈ nat.factors (nat_abs a) ∧ ↑n = x := mem_map

lemma prime_int_mem_factors {p : ℤ} {a : ℤ} : 
p ∈ prime_int_factors a → prime_int p := begin
rw prime_int_factors.mem,
rintro ⟨n, h1, h2⟩, 
rw h2.symm,
unfold prime_int,
rw nat_abs_of_nat,
exact nat.mem_factors h1,
end

lemma prime_int_factors_ne_zero (a : ℤ) : (prime_int_factors a).prod ≠ (0:ℤ) := begin
suffices h1 : (∀ (x : ℤ), x ∈ prime_int_factors a → x ≠ 0),
  have := list.prod_ne_zero _ _ (prime_int_factors a) h1,
  exact this, intros x y, exact mul_eq_zero.1, simp,
intros x h, 
exact prime_int_ne_zero (prime_int_mem_factors h),
end

lemma prime_int_factors_mem_pos {a : ℤ} : ∀ {p : ℤ}, p ∈ prime_int_factors a → 0 < p := begin
  intro p,
  intro Hp,
  change p ∈ map coe_t (nat.factors (nat_abs a)) at Hp,
  rw mem_map at Hp,
  cases Hp with q Hq,
  have Hq' : nat.prime q := nat.mem_factors Hq.1,
  replace Hq : (q : ℤ) = p := Hq.2,
  show ((0 : ℕ) : ℤ) < p,
  rw ←Hq,
  rw int.coe_nat_lt,
  exact nat.prime.pos Hq',
end

lemma prime_int_factors_prod_nonneg (a : ℤ) : 0 ≤ (prime_int_factors a).prod := begin
suffices h : ∀ (k : ℤ), k ∈ prime_int_factors a → 0 ≤ k,
  exact list.prod_nonneg_of_mem_nonneg h,
intros k h, exact (int.le_of_lt (prime_int_factors_mem_pos h)),
end

lemma prime_int_factors_prod {a : ℤ} (h : 0 < a) : (prime_int_factors a).prod = a := begin
have h1:= eq_nat_abs_of_zero_le (int.le_of_lt h), 
have h0 := h,
rw [h1, ←int.coe_nat_zero, int.coe_nat_lt] at h, 
have h2 := nat.prod_factors h,
unfold prime_int_factors, rw ←int.coe_nat_eq_coe_nat_iff at h2, 
conv {to_rhs, rw [h1, h2.symm]},
rw list.prod_cast _,
end

lemma prime_int_factors_mem_le_prod {a b : ℤ} (ha : 0 < a) (h : b ∈ prime_int_factors a) :
b ≤ a := begin
have := dvd_prod h, rw prime_int_factors_prod ha at this,
exact le_of_dvd ha this,
end

lemma dvd_four {a : ℕ} : a ∣ 4 → (a = 1 ∨ a = 2 ∨ a = 4) := begin
intro h, 
have ha := nat.le_of_dvd (show (4:ℕ) > 0, by norm_num) h,
rw le_iff_lt_or_eq at ha, cases ha,
rw [nat.lt_succ_iff, le_iff_lt_or_eq] at ha, cases ha,
rw [nat.lt_succ_iff, le_iff_lt_or_eq] at ha, cases ha,
rw [nat.lt_succ_iff, le_iff_lt_or_eq] at ha, cases ha,
rw [nat.lt_succ_iff, nat.le_zero_iff] at ha,
exfalso, rw ha at h, cases h with k hk, rw zero_mul at hk, norm_num at hk,
exact or.intro_left (a = 2 ∨ a = 4) ha,
rw [←or_assoc, or_comm, ←or_assoc], 
exact or.intro_right (a = 4 ∨ a = 1) ha,
exfalso, 
have : ¬ a ∣ 4 , {rw ha, norm_num},
exact absurd h this,
rw ←or_assoc,
exact or.intro_right (a = 1 ∨ a = 2) ha,
end


lemma coprime_four_and_odd {a : ℤ} (h : ¬ 2 ∣ a) : nat.coprime (nat_abs 4) (nat_abs a) := begin
by_contradiction h0,
have h1 := nat.gcd_dvd (nat_abs 4) (nat_abs a),
have h2 := dvd_four h1.1, cases h2,
exact absurd h2 h0,
cases h2, 
have : 2 ∣ a, 
{
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd, (show (2:ℤ) = ↑(2:ℕ), by refl),
  h2.symm, nat_abs_of_nat], 
  exact h1.2,
},
exact absurd this h,
have : 2 ∣ a, 
{
  suffices h3 : 4 ∣ a, 
    exact dvd.trans (show (2:ℤ) ∣ 4, from ⟨(2:ℤ),rfl⟩) h3, 
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd, (show (4:ℤ) = ↑(4:ℕ), by refl),
  h2.symm, nat_abs_of_nat], 
  exact h1.2,
},
exact absurd this h,
end

theorem eq_self_mod {n : ℤ} (x : ℤ) : x ≡ (x % n) [ZMOD n] :=
begin
  show x % n = (x % n) % n,
  rw mod_mod,
end

lemma lemma_xy {q n x y : ℤ} (h_q : q = x^2 + n*y^2) (hq : q = 4 ∧ n = 3)
(h_xy : nat.coprime (nat_abs x) (nat_abs y)): 
(x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := 
begin
  rw hq.1 at h_q,
  rw hq.2 at h_q,
  have h2 : x ^ 2 + 3 * y ^ 2 = 4 := h_q.symm,
    let x0 := int.nat_abs x,
  let y0 := int.nat_abs y,
  have Hx : ↑(x0 * x0) = x * x := int.nat_abs_mul_self,
  have Hy : ↑(y0 * y0) = y * y := int.nat_abs_mul_self,
  change x * (x * 1) + 3 * (y * (y * 1)) = 4 at h2,
  rw [mul_one,mul_one] at h2,
  rw [←Hx, ←Hy] at h2,
  change ↑(x0 * x0) + ((3 : ℕ) : ℤ) * ↑(y0 * y0) = (4 : ℕ) at h2,
  rw [←int.coe_nat_mul, ←int.coe_nat_add, int.coe_nat_eq_coe_nat_iff] at h2,
  suffices : x0 = 1 ∧ y0 = 1,
    split,
    { have H : x = ↑x0 ∨ x = -↑x0 := int.nat_abs_eq x,
      rw this.1 at H,
      exact H },
    { have H : y = ↑y0 ∨ y = -↑y0 := int.nat_abs_eq y,
      rw this.2 at H,
      exact H },
  clear Hx Hy,

  have Hx0 : x0 * x0 ≤ 2 * 2,
    show _ ≤ 4,
    rw ←h2,
    exact nat.le_add_right (x0 * x0) (3 * (y0 * y0)),
  have Hy0 : y0 * y0 ≤ 1 * 1,
    suffices : 3 * (y0 * y0) ≤ 4,
      rwa [mul_comm, ←nat.le_div_iff_mul_le] at this, exact dec_trivial,
    rw ←h2,
    apply nat.le_add_left,
  rw ←nat.mul_self_le_mul_self_iff at Hx0,
  rw ←nat.mul_self_le_mul_self_iff at Hy0,
  have H : nat.coprime x0 y0 := h_xy,
  revert H,
  revert h2,
  revert Hy0,
  generalize : y0 = y1,
  revert y1,
  revert Hx0,
  generalize : x0 = x1,
  revert x1,
  exact dec_trivial,
end


lemma int.coprime.dvd_of_dvd_mul_left {a b c : ℤ} (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
a ∣ b * c → a ∣ c := 
begin
intro, 
rw [← nat_abs_dvd, ← dvd_nat_abs, nat_abs_mul, coe_nat_dvd] at a_1,
have := nat.coprime.dvd_of_dvd_mul_left h_ab a_1,
rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs] at this,
exact this,
end

-- lemma prime_coprime {a b p : ℤ} (hp : prime_int p) (h_ab : a > 0 ∧ b > 0) :
-- p = a + b → nat.coprime (nat_abs a) (nat_abs b) := 
-- begin
-- intro h,
-- have h1:= nat.gcd_dvd (nat_abs a) (nat_abs b), 
-- rw [← coe_nat_dvd, dvd_nat_abs, ← coe_nat_dvd, dvd_nat_abs] at h1,
-- have h2:=dvd_add h1.1 h1.2, rw [h.symm, ← dvd_nat_abs, coe_nat_dvd] at h2,
-- have h3:= hp.2 (nat.gcd (nat_abs a) (nat_abs b)) h2,
-- cases h3, exact h3,
-- exfalso,
-- have h4 := and.intro (le_of_dvd h_ab.1 h1.1) (le_of_dvd h_ab.2 h1.2),
-- have h5 := add_le_add' h4.1 h4.2, 
-- rw [h.symm, h3, (mul_two ↑(nat_abs p)).symm] at h5,
-- have zero_lt_na_p : (0:ℤ) < (↑(nat_abs p) : ℤ), 
-- {
--   rw [(show (0:ℤ) = ↑(0:ℕ), by refl), int.coe_nat_lt, nat.pos_iff_ne_zero'],
--   suffices : p ≠ (0:ℤ),
--     exact nat_abs_ne_zero_of_ne_zero this,
--   exact prime_int_ne_zero hp,
-- },
-- have h6 : p ≤ ↑(nat_abs p), 
-- {
--   cases (nat_abs_eq p), finish,
--   rw [h_1, nat_abs_neg, nat_abs_of_nat],
--   suffices : (-1 : ℤ) * ↑(nat_abs p) ≤ (1 : ℤ) * ↑(nat_abs p),
--     simp at this, exact this,
--   rw (mul_le_mul_right zero_lt_na_p),
--   simp,
-- },
-- have h7 := le_trans h5 h6, exfalso,
-- have h8 : (↑(nat_abs p) : ℤ) ≠ (0 : ℤ),
-- {
--   suffices : p ≠ 0,
--     simp [nat_abs_ne_zero_of_ne_zero this],
--   exact prime_int_ne_zero hp,
-- },
-- have h9 := int.div_le_div zero_lt_na_p h7,
-- rw [(int.mul_div_cancel_left 2 h8), int.div_self h8] at h9,
-- exact h9,
-- end

lemma pos_int_pow_pos {a : ℤ} (ha : 0 < a) (k : ℕ) : 0 < a^k := begin
induction k with k h0,
simp,
rw [pow_succ, (mul_zero a).symm, mul_lt_mul_left ha],
exact h0,
end

lemma int.ne_zero_of_pos {a : ℤ} : 0 < a → a ≠ 0 :=
by {intro, unfold ne, by_contradiction, rw a_2 at a_1, exact a_1}

-- lemma residue_rewrite {a b n : ℤ} : a % n = b → ∃ k : ℤ, a = k * n + b := begin
-- intro, existsi (a/n), rw a_1.symm,
-- conv in (a) begin rw (int.mod_add_div a n).symm, end,
-- rw [mul_comm, add_comm],
-- end

lemma four_dvd_odd_add_or_sub {a b : ℤ} (h : a % 2 = 1 ∧ b % 2 = 1) : 4 ∣ (b - a) ∨ 4 ∣ (b + a) := begin
cases h with ha hb, 
rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at ha, 
rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at hb, 
cases ha with k ha, cases hb with l hb,
rw sub_eq_iff_eq_add at ha, rw sub_eq_iff_eq_add at hb,
cases (int.mod_two_eq_zero_or_one k) with hk,
rw ← dvd_iff_mod_eq_zero at hk, cases hk with t ht,
cases (int.mod_two_eq_zero_or_one l) with hl,
{
  rw ← dvd_iff_mod_eq_zero at hl, cases hl with s hs,
  have : b - a = 4 * (s - t), by {rw [hb, ha, ht, hs], ring},
  exact or.intro_left _ (dvd.intro _ this.symm),
},
{
  rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at h,
  cases h with s hs, rw sub_eq_iff_eq_add at hs,
  have : b + a = 4 * (s + t + 1), by {rw [hb, ha, ht, hs], ring,},
  exact or.intro_right _ (dvd.intro _ this.symm),
},
rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at h, 
cases h with t ht, rw sub_eq_iff_eq_add at ht,
cases (int.mod_two_eq_zero_or_one l) with hl,
{
  rw ← dvd_iff_mod_eq_zero at hl, cases hl with s hs,
  have : b + a = 4 * (s + t + 1), by {rw [hb, ha, ht, hs], ring,},
  exact or.intro_right _ (dvd.intro _ this.symm),
},
{
  rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at h,
  cases h with s hs, rw sub_eq_iff_eq_add at hs,
  have : b - a = 4 * (s - t), by {rw [hb, ha, ht, hs], ring,},
  exact or.intro_left _ (dvd.intro _ this.symm),
},
end

lemma not_even_of_coprime {a b : ℤ} : nat.coprime (nat_abs a) (nat_abs b) → ¬(a % 2 = 0 ∧ b % 2 = 0) := begin
intro h, by_contradiction, 
rw [←dvd_iff_mod_eq_zero, ←dvd_iff_mod_eq_zero, ←dvd_nat_abs, ← nat_abs_dvd,
coe_nat_dvd, ←dvd_nat_abs, ← nat_abs_dvd, coe_nat_dvd] at a_1,
have := nat.not_coprime_of_dvd_of_dvd
(show nat_abs (2:ℤ) > (1:ℕ), by {rw (show nat_abs 2 = (2:ℕ), by refl), norm_num,}) a_1.1 a_1.2,
exact absurd h this,
end

-- lemma coprime_nat_abs_one {x y : ℤ} (h_x : x = 1 ∨ x = -1) (h_y : y = 1 ∨ y = -1) : nat.coprime (nat_abs x) (nat_abs y) :=
-- begin 
-- cases h_x, cases h_y, 
-- rw [h_x, h_y], exact nat.gcd_self (nat_abs 1),
-- rw [h_x, h_y], exact nat.gcd_self (nat_abs 1),
-- cases h_y,
-- rw [h_x, h_y], exact nat.gcd_self (nat_abs 1),
-- rw [h_x, h_y], exact nat.gcd_self (nat_abs 1),
-- end

lemma gcd_dvd_mul_add_mul {a b c d q : ℤ} : (q = a * c + b * d) → ((gcd (nat_abs a) (nat_abs b) : ℤ)∣ q ):=
begin
have h1 := nat.gcd_dvd (nat_abs a) (nat_abs b),
rw [←coe_nat_dvd, ←coe_nat_dvd] at h1,
have h2 := and.intro (dvd_nat_abs.1 h1.1) (dvd_nat_abs.1 h1.2),
have h3 := and.intro (dvd_mul_of_dvd_left h2.1 c) (dvd_mul_of_dvd_left h2.2 d),
intro, rw a_1, exact (dvd_add h3.1 h3.2),
end

lemma coprime_lemma {a b c d k l m n : ℤ} (ha : a = c * k + d * l) (hb : b = c * m + d * n) :
nat.coprime (nat_abs a) (nat_abs b) → nat.coprime (nat_abs c) (nat_abs d) :=
begin
intro, by_contradiction, 
have h1 := nat.gcd_dvd (nat_abs c) (nat_abs d),
rw [←coe_nat_dvd, ←coe_nat_dvd] at h1,
have h2 := and.intro (dvd_nat_abs.1 h1.1) (dvd_nat_abs.1 h1.2),
have ha_dvd := and.intro (dvd_mul_of_dvd_left h2.1 k) (dvd_mul_of_dvd_left h2.2 l),
have hb_dvd := and.intro (dvd_mul_of_dvd_left h2.1 m) (dvd_mul_of_dvd_left h2.2 n),
have h_dvd := and.intro (dvd_add ha_dvd.1 ha_dvd.2) (dvd_add hb_dvd.1 hb_dvd.2),
rw [ha.symm, hb.symm] at h_dvd,
rw [← dvd_nat_abs, coe_nat_dvd, ← dvd_nat_abs, coe_nat_dvd] at h_dvd,
have h_g_one: nat.gcd (nat_abs c) (nat_abs d) > 1,
begin
    by_contradiction, rw [not_lt, (show (1:ℕ) = 0 + 1, by refl), nat.le_add_one_iff] at a_3,
    cases a_3, rw nat.le_zero_iff at a_3,
    have h := and.intro (nat.eq_zero_of_gcd_eq_zero_left a_3) (nat.eq_zero_of_gcd_eq_zero_right a_3),
    have := and.intro (eq_zero_of_nat_abs_eq_zero h.1) (eq_zero_of_nat_abs_eq_zero h.2),
    rw [this.1, this.2] at ha, rw [this.1, this.2] at hb,
    have h5 : nat.gcd (nat_abs a) (nat_abs b) = 0, {rw [ha, hb], simp},
    unfold nat.coprime at a_1, rw h5 at a_1, simp at a_1, exact a_1,
    exact absurd a_3 a_2,
end,
have := nat.not_coprime_of_dvd_of_dvd h_g_one h_dvd.1 h_dvd.2,
exact absurd a_1 this,
end

-- lemma gcd_le {a b : ℕ} (h_a : a ≠ 0) (h_b : b ≠ 0) : gcd a b ≤ a ∧ gcd a b ≤ b := 
-- begin
-- have := nat.gcd_dvd a b,
-- exact and.intro (nat.le_of_dvd (nat.pos_iff_ne_zero.2 h_a) this.1) (nat.le_of_dvd (nat.pos_iff_ne_zero.2 h_b) this.2),
-- end

-- lemma prime_coprime_mul {a b c d p : ℤ} (hp : prime_int p) : p = a * b + c * d → nat.coprime (nat_abs a) (nat_abs c) ∨ nat.gcd (nat_abs a) (nat_abs c) = nat_abs p:= 
-- begin
-- intro, unfold nat.coprime, unfold prime_int at hp, unfold nat.prime at hp,
-- have h1 := gcd_dvd_mul_add_mul a_1, rw [← dvd_nat_abs, coe_nat_dvd] at h1,
-- have := hp.2 (gcd (nat_abs a) (nat_abs c)) h1,
-- exact this,
-- end

lemma prime_int_dvd_mul {p m n : ℤ} (pp : prime_int p): 
p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
begin
{
  suffices : ↑(nat_abs p) ∣ m * n ↔ ↑(nat_abs p) ∣ m ∨ ↑(nat_abs p) ∣ n,
    rw [nat_abs_dvd, nat_abs_dvd, nat_abs_dvd] at this,
    exact this,
  rw [←dvd_nat_abs, coe_nat_dvd, nat_abs_mul, ←dvd_nat_abs,
  coe_nat_dvd, ←dvd_nat_abs, coe_nat_dvd],
  exact @nat.prime.dvd_mul _ _ _ pp,
},
end


lemma four_dvd_of_two_dvd {a b : ℤ} (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
2 ∣ a^2 + 3 * b^2 → 4 ∣ a^2 + 3 * b^2 := begin
intro h,
suffices h0 : a % 2 = 1 ∧ b % 2 = 1, 
  rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero,
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at h0,
  cases h0.1 with k hk, cases h0.2 with l hl,
  rw sub_eq_iff_eq_add at hk, rw sub_eq_iff_eq_add at hl,
  rw [hk, hl, (show (2 * k + 1) ^ 2 + 3 * (2 * l + 1) ^ 2 = 4 * (k^2 + k + 3*l^2 + 3*l + 1), by ring)], simp,
cases (int.mod_two_eq_zero_or_one a) with ha ha,
cases (int.mod_two_eq_zero_or_one b) with hb hb,
{
  exfalso, exact absurd (and.intro ha hb) (not_even_of_coprime h_ab),
},
{
  exfalso, 
  rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at hb,
  rw ←dvd_iff_mod_eq_zero at ha,
  cases ha with k hk, cases hb with l hl,
  rw sub_eq_iff_eq_add at hl,
  rw [hk, hl, (show (2 * k) ^ 2 + 3 * (2 * l + 1) ^ 2 = 2 * (2 * k^2 + 3 * 2 * l^2 + 3 * 2 * l + 1) + 1, by ring), 
  ←(dvd_add_iff_right _)] at h, 
  have := eq_one_of_dvd_one _ h, norm_num at this, norm_num, simp,
},
cases (int.mod_two_eq_zero_or_one b) with hb hb,
{
  exfalso, 
  rw [(show (1:ℤ) = 1 % 2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, ←dvd_iff_mod_eq_zero] at ha,
  rw ←dvd_iff_mod_eq_zero at hb,
  cases ha with k hk, cases hb with l hl,
  rw sub_eq_iff_eq_add at hk,
  rw [hk, hl, (show (2 * k + 1) ^ 2 + 3 * (2 * l) ^ 2 = 2 * ( 2 * k^2 + 2 * k + 3 * 2 * l^2) + 1, by ring), 
  ←(dvd_add_iff_right _)] at h, 
  have := eq_one_of_dvd_one _ h, norm_num at this, norm_num, simp,
},
exact and.intro ha hb,
end

------------ lemmas for descent step ------------------


lemma lemma_1 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2)
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)):
(prime_int q ∨ q = 4 ∧ n = 3) → q ∣  n * (x*b - a*y) * (x*b + a*y) :=
begin
intro,
have h1 : q ∣ a^2 *(x^2 + n*y^2), {rw h_q, exact (dvd_mul_left _ _)},
have h2 := dvd_sub (dvd_mul_of_dvd_right h_q_dvd _) h1, 
have h3 : x ^ 2 * (a ^ 2 + n * b ^ 2) - a ^ 2 * (x ^ 2 + n * y ^ 2) = n*(x*b - a*y)*(x*b + a*y), by ring,
rw h3.symm, exact h2,
end

lemma lemma_2 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2)
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b))
(a_1 : prime_int q ∨ q = 4 ∧ n = 3) (h1 :  q ∣ x * b - a * y)
(h_xy : nat.coprime (nat_abs x) (nat_abs y)) : 
∃ (c d : ℤ), (a ^ 2 + n * b ^ 2) / q = c ^ 2 + n * d ^ 2 ∧ nat.coprime (nat_abs c) (nat_abs d) :=
begin
cases h1 with d hd, cases (dec_em (x = 0)), cases a_1,

have h_qn : q = n, begin
  rw h at h_q,
  ring at h_q,
  have h1:= dvd.intro_left (y^2) h_q.symm,
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at h1,
  replace h1 := a_1.2 (nat_abs n) h1,
  cases h1,
  exfalso, cases (nat_abs_eq n) with h2,
  rw [h2, h1, (show y^2 * ↑(1:ℕ) = y^2, by simp)] at h_q,
  exact prime_int_not_square a_1 y h_q,
  rw h1 at h_1, rw [h_1, (neg_mul_eq_mul_neg (y^2) (↑1)).symm] at h_q,
  unfold prime_int at a_1,
  rw (nat_abs_neg q).symm at a_1,
  replace h_q : -q = y ^ 2, {rw h_q, simp},
  exact prime_int_not_square a_1 y h_q,
  have hn := eq_nat_abs_of_zero_le ((le_iff_eq_or_lt).2 (or.intro_right (0 = n) h_n)),
  have h2 : 0 ≤ y^2, by {rw (show y^2 = y * y, by ring), exact mul_self_nonneg y},
  have := (mul_le_mul_right h_n).2 h2,
  rw [h_q.symm, zero_mul] at this,
  have hq := eq_nat_abs_of_zero_le this,
  rw [hq, hn, int.coe_nat_eq_coe_nat_iff],
  exact h1.symm,
end,
rw h_qn at a_1,
rw [h_qn, ←(dvd_add_iff_left (dvd_mul_right n (b^2))), (show a^2 = a*a, by ring),
(prime_int_dvd_mul a_1), or_self] at h_q_dvd,
cases h_q_dvd with d hd,
existsi b, existsi d, split, 
rw [hd, h_qn, (show (n * d) ^ 2 + n * b ^ 2 = n * (b ^ 2 + n * d ^ 2), by ring), 
int.mul_div_cancel_left _ (int.ne_zero_of_pos h_n)],
have h_dvd:= (dvd_of_mul_left_eq n hd.symm),
rw [←dvd_nat_abs, ←nat_abs_dvd, int.coe_nat_dvd] at h_dvd,
exact nat.coprime.symm (nat.coprime.coprime_dvd_left h_dvd h_ab),

exfalso, rw [h, a_1.1, a_1.2, (show 0 ^ 2 + 3 * y ^ 2 = 3*y^2, by ring)] at h_q,
have := (dvd.intro (y^2) h_q.symm), 
revert this, exact dec_trivial,

have h1: x * (b - d * x) = y * (a + n * d * y), begin
  rw [h_q, sub_eq_iff_eq_add] at hd,
  rw [mul_sub_left_distrib, hd], ring,
end,
cases (int.coprime.dvd_of_dvd_mul_left h_xy (dvd.intro _ h1)) with c h2,
have ha := eq_sub_iff_add_eq.2 h2,
rw h2 at h1,
have hb : b = c*y + d*x,
{
  rw [mul_sub_left_distrib, sub_eq_iff_eq_add, 
  (show y * (x * c) + x * (d * x) = x * (c*y + d*x), by ring)] at h1,
  exact eq_of_mul_eq_mul_left h h1,
},
have identity := identity c d n x y,
rw [h_q.symm, ha.symm, hb.symm] at identity,
existsi c, existsi d,
split,
have q_ne_zero : q ≠ 0, 
{
  unfold ne, by_contradiction,
  cases a_1,
  exact absurd a_2 (prime_int_ne_zero a_1),
  rw a_1.1 at a_2, norm_num at a_2,
},
exact (int.div_eq_iff_eq_mul_left q_ne_zero (dvd.intro_left _ identity)).2 identity.symm,
have h_a : a = c * x + d * (-n * y), {rw ha, ring},
exact coprime_lemma h_a hb h_ab,
end

lemma lemma_3 {q n x y a b : ℤ} (h_x : x = 1 ∨ x = -1) (h_y : y = 1 ∨ y = -1) :
4 ∣ (x * b - a * y) * (x * b + a * y) → 4 ∣ (b - a) * (b + a) := 
begin 
intro,
cases h_x, cases h_y,
rw [h_x, h_y, 
(show (1 * b - a * 1) * (1 * b + a * 1) = (b - a) * (b + a), by ring)] at a_1, exact a_1,
rw [h_x, h_y, 
(show (1 * b - a * -1) * (1 * b + a * -1) = (b - a) * (b + a), by ring)] at a_1, exact a_1,
cases h_y,
rw [h_x, h_y, 
(show ((-1) * b - a * 1) * ((-1) * b + a * 1) = (b - a) * (b + a), by ring)] at a_1, exact a_1,
rw [h_x, h_y, 
(show ((-1) * b - a * -1) * ((-1) * b + a * -1) = (b - a) * (b + a), by ring)] at a_1, exact a_1,
end

lemma lemma_4 {a b n q : ℤ} (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) :
(q = (4:ℤ) ∧ n = (3:ℤ)) → (a % 2 = 1 ∧ b % 2 = 1) := begin
intro h,
rw [h.1, h.2] at h_q_dvd,

rcases (int.mod_two_eq_zero_or_one a) with ha, exfalso,
have hb := or_iff_not_imp_left.1 (int.mod_two_eq_zero_or_one b) (not_and.1 (not_even_of_coprime h_ab) ha),
cases (dvd_of_mod_eq_zero ha) with k hk,
replace hb := eq.trans hb (show (1:ℤ) = (1:ℤ) % (2:ℤ), by refl),
cases (dvd_of_mod_eq_zero (mod_eq_mod_iff_mod_sub_eq_zero.1 hb)) with l hl,
rw sub_eq_iff_eq_add at hl, 
rw [hl, hk, (show (2 * k) ^ 2 + (3:ℤ) * (2 * l + 1) ^ 2 = 4 * (k^2 + 3*l^2 + 3*l) + (3:ℤ), by ring)] at h_q_dvd, 
replace h_q_dvd := (dvd_add_iff_right (dvd_mul_right (4:ℤ) (k ^ 2 + 3 * l ^ 2 + 3 * l))).2 h_q_dvd,
have : ¬ (4:ℤ) ∣ (3:ℤ), {exfalso, have := le_of_dvd _ h_q_dvd, exact this, norm_num},
exact absurd h_q_dvd this,

replace h_1 := eq.trans h_1 (show (1:ℤ) = (1:ℤ) % (2:ℤ), by refl),
cases (dvd_of_mod_eq_zero (mod_eq_mod_iff_mod_sub_eq_zero.1 h_1)) with k hk,
rw sub_eq_iff_eq_add at hk, rw hk at h_q_dvd,

cases (int.mod_two_eq_zero_or_one b) with hb, exfalso,
cases (dvd_of_mod_eq_zero hb) with l hl,
rw [hl, (show (2 * k + 1) ^ 2 + 3 * (2 * l) ^ 2 = 4 * (k^2 + k + 3*l^2) + 1, by ring)] at h_q_dvd,
replace h_q_dvd := (dvd_add_iff_right (dvd_mul_right 4 (k ^ 2 + k + 3 * l ^ 2))).2 h_q_dvd,
have : ¬ (4:ℤ) ∣ (1:ℤ), {exfalso, have :=le_of_dvd _ h_q_dvd, exact this, norm_num},
exact absurd h_q_dvd this,
exact and.intro h_1 h_2,
end

lemma lemma_5 {q n x y : ℤ} (hq : prime_int q) (hn : 0 < n) (h : q ∣ n) (h1 : q = x^2 + n*y^2) :
q = n := begin
cases (dec_em (y = 0)) with hy,
{
  exfalso, rw hy at h1, ring at h1,
  exact prime_int_not_square hq x h1,
},
{
  suffices h0 : n ≤ q, 
    exact (le_antisymm h0 (le_of_dvd hn h)).symm,
  have hy : 0 ≠ y * y, by {unfold ne, by_contradiction, replace a := a.symm, rw [mul_eq_zero, or_self] at a, exact absurd a h_1},
  have h2:= add_one_le_of_lt (lt_of_le_of_ne (mul_self_nonneg y) hy),
  have h3:= le_add_of_nonneg_of_le' (mul_self_nonneg x) ((le_mul_iff_one_le_right hn).2 h2), 
  convert h3, rw h1, ring,
},
end


lemma lemma_q_prime {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2)
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) 
(h_xy : nat.coprime (nat_abs x) (nat_abs y)): 
prime_int q → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (nat.coprime (nat_abs c) (nat_abs d))) := 
begin
intro,
have zero_le_q := nonneg_int h_n h_q,
have h1 := (prime_int_dvd_mul a_1).1 (lemma_1 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1)),
cases h1, rw (prime_int_dvd_mul a_1) at h1,
----
cases h1,
have h2 := lemma_5 a_1 h_n h1 h_q,
rw h2 at h_q_dvd, rw h2 at h_q, rw h2 at a_1,
have h3 := (dvd_add_iff_left (dvd_mul_right n (b^2))).2 h_q_dvd,
rw [((show a^2 = a*a, by ring)), (prime_int_dvd_mul a_1), or_self] at h3,
rcases (exists_eq_mul_right_of_dvd h3) with d,
let c := b,
rcases (exists_eq_mul_right_of_dvd h_q_dvd) with m,
have h4 := int.ne_zero_of_pos h_n,
rw ← (int.div_eq_iff_eq_mul_right h4 h_q_dvd) at h_1,
have b_1 := h_1,
rw [(int.add_mul_div_left _ _ h4), (show a^2 = a* a, by ring), h, 
(show b = c, by refl), (show n * d * (n * d) = (n * d) * n * d, by ring)] at h_1,
have h_11 : n * d * n * d / n + c ^ 2  = c ^ 2 + n * d * (n * d / n), by
{
  rw [add_comm, add_left_inj, mul_assoc,
  (int.mul_div_cancel_left d h4)],
  conv in (n * d * (n * d)) begin rw mul_assoc, end,
  rw (int.mul_div_cancel_left (d * (n * d)) h4), ring,
},
rw [h_11, (@int.mul_div_cancel_left n d h4), (show n*d*d = n*(d*d), by ring),
(show d*d = d^2, by ring)] at h_1,
rw [h2.symm, h_1.symm, (show (a ^ 2 + q * b ^ 2) = (a ^ 2 + n * b ^ 2), by {rw h2})] at b_1,
existsi c, existsi d, split, exact b_1, 
---
rw [(show c = b, by refl), (int.div_eq_of_eq_mul_right h4 h).symm],
have h5: nat_abs a = (nat_abs (a / n)) * (nat_abs n), 
{rw [(nat_abs_mul (a/n) n).symm, (int.div_mul_cancel h3)]},
replace h5 : (nat_abs (a / n)) ∣ (nat_abs a), 
{rw h5, exact dvd_mul_right (nat_abs (a/n)) (nat_abs n)},
exact nat.coprime.coprime_dvd_right (h5) (nat.coprime.symm h_ab),
-----
exact (lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1 h_xy),
-----
let y_ := -y, rw (show y^2 = y_^2, by norm_num) at h_q,
rw [(show a*y = -a * y_, by simp), ←neg_mul_eq_neg_mul, ←sub_eq_add_neg] at h1,
rw [(show y = -y_, by simp), nat_abs_neg] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1 h_xy,
end


lemma lemma_q_4_n_3 {q n x y a b : ℤ} (h_q : q = x^2 + n*y^2) (h_xy : nat.coprime (nat_abs x) (nat_abs y))
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
(q = (4:ℤ) ∧ n = (3:ℤ)) → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (nat.coprime (nat_abs c) (nat_abs d))) := 
begin
intro, 
have h_n : (0: ℤ) < n, by {rw a_1.2, norm_num},
let x_ := -x, let y_ := -y,
have hx : x = -x_, by simp, have hy : y = -y_, by simp,
have hx_ : x_ = -x, by simp, have hy_ : y_ = -y, by simp,
have hx2 : x^2 = x_^2, by norm_num, have hy2 : y^2 = y_^2, by norm_num,
have h1 := lemma_4 h_q_dvd h_ab a_1,
have h_x_y := lemma_xy h_q a_1 h_xy,
have h_x := h_x_y.1, have h_y := h_x_y.2,
have h2 := four_dvd_odd_add_or_sub h1,
cases h2, cases h_x, cases h_y,
have h3 : q ∣ x*b - a*y, {rw [h_x, h_y, a_1.1, mul_one, one_mul], exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy, 
rw hy2 at h_q,
have h_y_ : y_ = 1, {rw [hy_, h_y], simp},
have h3 : q ∣ x*b - a*y_, {rw h_x, rw h_y_, simp, rw a_1.1, exact h2},
rw [hy, nat_abs_neg] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
cases h_y,
rw hx2 at h_q,
have h_x_ : x_ = 1, {rw [hx_, h_x], simp},
have h3 : q ∣ x_*b - a*y, {rw h_y, rw h_x_, simp, rw a_1.1, exact h2},
rw [hx, nat_abs_neg] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
rw hx2 at h_q,
have h_x_ : x_ = 1, {rw [hx_, h_x], simp},
rw hy2 at h_q,
have h_y_ : y_ = 1, {rw [hy_, h_y], simp},
have h3 : q ∣ x_*b - a*y_, {rw h_y_, rw h_x_, simp, rw a_1.1, exact h2},
rw [hx, hy, nat_abs_neg, (nat_abs_neg y_)] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
cases h_x, cases h_y,
rw hy2 at h_q,
have h_y_ : y_ = -1, {rw [hy_, h_y]},
have h3 : q ∣ x*b - a*y_,
{rw h_y_, rw h_x, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
rw [hy, nat_abs_neg] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
have h3 : q ∣ x*b - a*y, {rw h_y, rw h_x, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
cases h_y,
rw hx2 at h_q,
have h_x_ : x_ = 1, {rw [hx_, h_x], simp},
rw hy2 at h_q,
have h_y_ : y_ = -1, {rw [hy_, h_y]},
have h3 : q ∣ x_*b - a*y_, {rw h_y_, rw h_x_, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
rw [hx, hy, nat_abs_neg, (nat_abs_neg y_)] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
rw hx2 at h_q,
have h_x_ : x_ = 1, {rw [hx_, h_x], simp},
have h3 : q ∣ x_*b - a*y, {rw h_y, rw h_x_, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
rw [hx, nat_abs_neg] at h_xy,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3 h_xy,
end


definition int.div' (a : ℤ) (p : ℤ) : ℤ :=
if a % p ≤ (p / 2) then a / p else (a / p) + 1

definition int.mod' (a : ℤ) (p : ℤ) : ℤ :=
if a % p ≤ (p / 2) then a % p else (a % p) - p

lemma int.mod_add_div' (a p : ℤ) :
int.mod' a p + p * (int.div' a p) = a :=
begin
  unfold int.mod' int.div',
  split_ifs,
    rw int.mod_add_div,
  suffices : a % p - p + p * (a / p + 1) = a % p + p * (a / p),
    rw [this,int.mod_add_div],
  rw [mul_add,mul_one,add_comm _ p,←add_assoc],congr',simp,
end


lemma mul_lt_of_le_div (b p : ℤ) (h0 : p % 2 = 1) : b ≤ p / 2 → 2 * b < p := begin
  intro H,
  rw ←(int.mod_add_div p 2),
  rw h0,
  rw add_comm,
  apply lt_add_of_le_of_pos _ zero_lt_one,
  apply mul_le_mul_of_nonneg_left H,
  exact dec_trivial
end


lemma int.mod'_lt_p_div_two (a p : ℤ) (h : 0 < p) (h0 : p % 2 = 1):
2 * abs (int.mod' a p) <  p :=
begin
  apply mul_lt_of_le_div _ _ h0,
  have hp' : p ≠ 0 := λ hn, by rw hn at h;cases h,
  rw abs_le,
  unfold int.mod',
  split_ifs with h1,
    split,
      apply le_trans _ (_ : 0 ≤ a % p),
        rw [←neg_nonneg,neg_neg],
        exact int.div_nonneg (int.le_of_lt h) (dec_trivial),
      refine int.mod_nonneg a hp',
    exact h1,
  rw not_le at h1,
  split,
  rw le_sub_iff_add_le,
  suffices : -(p / 2) + p ≤ (p / 2) + 1,
    exact le_trans this h1,
    rw [neg_add_le_iff_le_add,←add_assoc,←two_mul],
    suffices : 2 * (p / 2) + p % 2 ≤ 2 * (p / 2) + 1,
      convert this,
      rw [add_comm,int.mod_add_div],
    apply add_le_add_left,
    apply int.le_of_lt_add_one,
    exact int.mod_lt p (dec_trivial : (2 : ℤ) ≠ 0),
  rw sub_le_iff_le_add,
  refine le_trans (int.le_of_lt $ int.mod_lt a hp') _,
  rw abs_of_pos h,
  apply le_add_of_nonneg_left,
  exact int.div_nonneg (int.le_of_lt h) dec_trivial,
end


lemma int.zero_pow {n : ℕ} (hn : n ≠ 0) : (0:ℤ)^n = 0 := begin
rw [(@nat.sub_add_cancel n (1:ℕ) _).symm, pow_succ, zero_mul], 
by_contradiction, rw [not_le, nat.lt_succ_iff, nat.le_zero_iff] at a,
exact absurd a hn,
end

lemma int.div_pow {a b : ℤ} {n : ℕ} (h : b ∣ a) (hb : b ≠ 0) : 
(a/b)^n = a^n /  b^n := begin
cases (dec_em (n = 0)) with hn hn,
rw [hn, pow_zero], simp,
cases h with k h,
rw [h, int.mul_div_cancel_left _ hb, mul_pow, int.mul_div_cancel_left],
exact pow_ne_zero n hb,
end


lemma lemma_dvd_add_left {a b c n : ℤ} (k : ℤ) (h_dvd : a ∣ b^2 + n * c^2) :
a ∣ (b + k*a)^2 + n * c^2 := begin
conv in ((b + k*a)^2) begin
rw (show (b + k*a)^2 = a * (2 * b * k + k * k * a) + b^2, by ring),
end,
rw [add_assoc, ←(dvd_add_iff_left h_dvd)],
exact (dvd_mul_right _ _),
end


lemma lemma_dvd_add_right {a b c n : ℤ} (k : ℤ) (h_dvd : a ∣ b^2 + n * c^2) :
a ∣ b^2 + n * (c + k*a)^2 := begin
conv in (n*(c + k * a) ^ 2) begin
rw (show n * (c + k * a) ^ 2 = n * c^2 + a * (n * 2 * c * k + n * k * k * a), by ring),
end,
rw [←add_assoc, ←(dvd_add_iff_right h_dvd)],
exact (dvd_mul_right _ _),
end

lemma lemma_dvd_div {a b c n l : ℤ} (h_dvd : a ∣ b^2 + n * c^2) (hl2_dvd : l^2 ∣ b^2 + n * c^2)
(h_lb : l ∣ b) (h_lc : l ∣ c) (h_pl : nat.coprime (nat_abs a) (nat_abs l)) 
(hl : 0 < l) (hb : 0 ≤ b) (hc : 0 ≤ c) :
a ∣ (b/l)^2 + n * (c/l)^2 := begin
rw [←int.mul_div_cancel_left (b^2 + n * c^2) (pow_ne_zero 2 (int.ne_zero_of_pos hl)), int.mul_div_assoc _ hl2_dvd] at h_dvd,
have h_pl2 := nat.coprime.pow_right (2:ℕ) h_pl, 
rw [nat.pow_two, ←nat_abs_mul, ←pow_two] at h_pl2,
have h := int.coprime.dvd_of_dvd_mul_left h_pl2 h_dvd, 
have h1 := mul_dvd_mul h_lb h_lb, rw [←pow_two, ←pow_two] at h1,
have h2 := mul_dvd_mul h_lc h_lc, rw [←pow_two, ←pow_two] at h2,
have := int.add_div_of_dvd_left (n * c^2) h1 (pow_ne_zero (2:ℕ) (int.ne_zero_of_pos hl)),
rw [int.div_pow h_lb (int.ne_zero_of_pos hl), int.div_pow h_lc (int.ne_zero_of_pos hl), 
(int.mul_div_assoc n h2).symm, this.symm],
exact h,
end 

lemma lemma_6 {a b : ℤ} {l : ℕ} (n : ℤ) (hl : l = nat.gcd (nat_abs a) (nat_abs b)) :
(↑l)^2 ∣ a^2 + n * b^2 := begin
have h := nat.gcd_dvd (nat_abs a) (nat_abs b), 
rw [←coe_nat_dvd, ←coe_nat_dvd, ←hl] at h,
replace h := and.intro (mul_dvd_mul h.1 h.1) (dvd_mul_of_dvd_right (mul_dvd_mul h.2 h.2) n),
rw [←int.coe_nat_mul, ←int.coe_nat_mul, ←int.coe_nat_mul, nat_abs_mul_self, 
nat_abs_mul_self, ←pow_two, ←pow_two, ←pow_two] at h,
exact dvd_add h.1 h.2,
end

lemma lemma_7 {a b p : ℤ} (hp : prime_int p) (h_ab : nat.coprime (nat_abs a) (nat_abs b)):
nat.coprime (nat_abs p) (nat_abs (nat.gcd (nat_abs (int.mod' a p)) (nat_abs (int.mod' b p)))) := begin
rw [(nat.prime.coprime_iff_not_dvd hp), nat_abs_of_nat],
by_contradiction h0,
have ha : nat_abs p ∣ nat_abs a, 
{
  suffices h : p ∣ int.mod' a p, 
    rw [←coe_nat_dvd, nat_abs_dvd, dvd_nat_abs],
    unfold int.mod' at h, split_ifs at h, 
    rw [mod_def, (show a - p * (a / p) = a + p * -(a/p), by simp)] at h, 
    exact (dvd_add_iff_left (dvd_mul_right _ _)).2 h, 
    rw [mod_def, (show a - p * (a / p) - p = a + p * (-(a/p) + -1), by {rw left_distrib, simp})] at h,
    exact (dvd_add_iff_left (dvd_mul_right _ _)).2 h,
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd],
  exact dvd.trans h0 (nat.gcd_dvd_left _ _),
},
have hb : nat_abs p ∣ nat_abs b, 
{
  suffices h : p ∣ int.mod' b p, 
    rw [←coe_nat_dvd, nat_abs_dvd, dvd_nat_abs],
    unfold int.mod' at h, split_ifs at h, 
    rw [mod_def, (show b - p * (b / p) = b + p * -(b/p), by simp)] at h, 
    exact (dvd_add_iff_left (dvd_mul_right _ _)).2 h, 
    rw [mod_def, (show b - p * (b / p) - p = b + p * (-(b/p) + -1), by {rw left_distrib, simp})] at h,
    exact (dvd_add_iff_left (dvd_mul_right _ _)).2 h,
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd],
  exact dvd.trans h0 (nat.gcd_dvd_right _ _),
},
have h1: nat_abs p > 1, 
{
  unfold prime_int at hp,
  by_contradiction h, norm_num at h, 
  rw le_iff_eq_or_lt at h, cases h, 
  rw h at hp, exact absurd hp (nat.not_prime_one),
  rw [nat.lt_succ_iff, nat.le_zero_iff] at h,
  rw h at hp, exact absurd hp (nat.not_prime_zero),
},
exact absurd h_ab (nat.not_coprime_of_dvd_of_dvd h1 ha hb),
end

lemma lemma_l_pos {a b p : ℤ} (h_0ltp : 0 < p) (hp : prime_int p) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) :
(0:ℕ) < nat.gcd (nat_abs (int.mod' a p)) (nat_abs (int.mod' b p)) := begin
suffices h0 : ¬ (int.mod' a p = 0 ∧ int.mod' b p = 0),
  by_contradiction h, norm_num at h, rw [nat.le_zero_iff] at h,
  have := and.intro (nat.eq_zero_of_gcd_eq_zero_left h) (nat.eq_zero_of_gcd_eq_zero_right h),
  replace this := and.intro (eq_zero_of_nat_abs_eq_zero this.1) (eq_zero_of_nat_abs_eq_zero this.2),
  exact absurd this h0,
by_contradiction h0,
unfold int.mod' at h0, split_ifs at h0 with h1, 
rw [←dvd_iff_mod_eq_zero, ←dvd_iff_mod_eq_zero, ←nat_abs_dvd, 
←dvd_nat_abs, coe_nat_dvd, ←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at h0,
unfold nat.coprime at h_ab, unfold prime_int at hp,
have := nat.dvd_gcd h0.1 h0.2, rw h_ab at this,
rw (nat.eq_one_of_dvd_one this) at hp,
exact absurd hp (nat.not_prime_one),
have h2 := mod_lt_of_pos b h_0ltp,
rw (sub_eq_iff_eq_add.1 h0.2) at h2,
exact absurd h2 (show ¬ 0 + p < p, by norm_num),
have h2 := mod_lt_of_pos a h_0ltp,
rw (sub_eq_iff_eq_add.1 h0.1) at h2,
exact absurd h2 (show ¬ 0 + p < p, by norm_num),
have h2 := mod_lt_of_pos b h_0ltp,
rw (sub_eq_iff_eq_add.1 h0.2) at h2,
exact absurd h2 (show ¬ 0 + p < p, by norm_num),
end

lemma lemma_8 {p n a b : ℤ} (h_n : (0: ℤ) < n) (zero_lt_p : 0 < p)
(hp : prime_int p ∧ nat_abs p ≠ 2) (h_p_dvd : p ∣ (a^2 + n*b^2))
(h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
∃ a_ b_ : ℤ, (p ∣ a_^2 + n * b_^2 ∧ (nat.coprime (nat_abs a_) (nat_abs b_)) ∧
2 * abs a_ < p ∧ 2 * abs b_ < p) := begin
let l := nat.gcd (nat_abs (int.mod' a p)) (nat_abs (int.mod' b p)),
have hl : l = (nat.gcd (nat_abs (int.mod' a p)) (nat_abs (int.mod' b p))), by refl,
have lpos := lemma_l_pos zero_lt_p hp.1 h_ab,
existsi ((int.mod' a p)/l), existsi ((int.mod' b p)/l),
have a1 : ↑l ∣ int.mod' a p, {rw [←dvd_nat_abs, int.coe_nat_dvd, hl], exact nat.gcd_dvd_left _ _,},
have a2 : ↑l ∣ int.mod' b p, {rw [←dvd_nat_abs, int.coe_nat_dvd, hl], exact nat.gcd_dvd_right _ _,},    
split,
{
  suffices h0 : p ∣ (↑(nat_abs (int.mod' a p))) ^ 2 + n * (↑(nat_abs (int.mod' b p))) ^ 2, 
    have a3 := lemma_7 hp.1 h_ab, rw hl.symm at a3,
    rw [hl.symm, ←coe_nat_lt] at lpos,
    have a5 : (0:ℤ) ≤ ↑(nat_abs (int.mod' a p)), by {rw [←int.coe_nat_zero, coe_nat_le], exact nat.zero_le _,},
    have a6 : (0:ℤ) ≤ ↑(nat_abs (int.mod' b p)), by {rw [←int.coe_nat_zero, coe_nat_le], exact nat.zero_le _,},
    have := lemma_dvd_div h0 (lemma_6 n hl) (dvd_nat_abs.2 a1) (dvd_nat_abs.2 a2) a3 lpos a5 a6, 
    rw [int.div_pow (dvd_nat_abs.2 a1) (int.ne_zero_of_pos lpos), int.div_pow (dvd_nat_abs.2 a2) (int.ne_zero_of_pos lpos), 
    pow_two, ←int.coe_nat_mul, nat_abs_mul_self, 
    ←pow_two, pow_two ↑(nat_abs (int.mod' b p)), ←int.coe_nat_mul, 
    nat_abs_mul_self, ←pow_two, ←(int.div_pow a1 (int.ne_zero_of_pos lpos)),
    ←(int.div_pow a2 (int.ne_zero_of_pos lpos))] at this,
    exact this, 
  rw [pow_two, pow_two, ←int.coe_nat_mul, ←int.coe_nat_mul, 
  nat_abs_mul_self, nat_abs_mul_self, ←pow_two, ←pow_two],
  have h : p ∣ (a % p)^2 + n * (b % p)^2, 
  {
    rw [mod_def, mod_def, mul_comm, mul_comm p (b/p), sub_eq_add_neg, sub_eq_add_neg, 
    (show -(a / p * p) = -(a / p) * p, by simp), 
    (show -(b / p * p) = -(b / p) * p, by simp)],
    exact lemma_dvd_add_right (-(b / p)) (lemma_dvd_add_left (-(a / p)) h_p_dvd),
  },
  unfold int.mod', split_ifs, exact h,
  have := lemma_dvd_add_right (-1:ℤ) h, rw neg_one_mul at this, exact this,
  have := lemma_dvd_add_left (-1:ℤ) h, rw neg_one_mul at this, exact this,
  have := lemma_dvd_add_left (-1:ℤ) (lemma_dvd_add_right (-1:ℤ) h), rw neg_one_mul at this, exact this,
},
{
  split, rw [hl, nat_abs_div, nat_abs_of_nat, nat_abs_div, nat_abs_of_nat],
  exact nat.coprime_div_gcd_div_gcd (lemma_l_pos zero_lt_p hp.1 h_ab),
  rw [←dvd_nat_abs, coe_nat_dvd], 
  simp [nat.gcd_dvd_right],
  rw [←dvd_nat_abs, coe_nat_dvd], 
  simp [nat.gcd_dvd_left],
  rw [hl.symm] at lpos,
  have h0 := and.intro (int.mod'_lt_p_div_two a p zero_lt_p (odd_prime_int_is_odd hp)) 
  (int.mod'_lt_p_div_two b p zero_lt_p (odd_prime_int_is_odd hp)),
  replace h0 := and.intro (lt_of_le_of_lt (int.div_le_self (↑l) _) h0.1) 
  (lt_of_le_of_lt (int.div_le_self (↑l) _) h0.2),
  rw [int.abs_div a1, int.abs_div a2, ←int.mul_div_assoc, 
  ←int.mul_div_assoc, abs_eq_nat_abs (↑l), nat_abs_of_nat],
  exact h0,
  rw [abs_eq_nat_abs, abs_eq_nat_abs, nat_abs_dvd, dvd_nat_abs], exact a2,
  rw [abs_eq_nat_abs, abs_eq_nat_abs, nat_abs_dvd, dvd_nat_abs], exact a1,
  exact zero_le_mul (show (0:ℤ) ≤ 2, by norm_num) (abs_nonneg _),
  exact zero_le_mul (show (0:ℤ) ≤ 2, by norm_num) (abs_nonneg _),
},
end

lemma lemma_9 {a : ℤ} (h : a % 2 = 1) (ha : 1 ≤ a): (a/2)^2 + 3* (a/2)^2 < a^2 := begin
conv in ((a/2)^2) begin rw (one_mul ((a / 2) ^ 2)).symm, end,
rw [←right_distrib, pow_two, pow_two, 
(show ((1:ℤ) + 3) * (a / 2 * (a / 2)) = 2 * (2 * (a/2))*(a/2), by {rw [←mul_assoc, ←mul_assoc], ring,})],
rw [mod_def, sub_eq_iff_eq_add, ←sub_eq_iff_eq_add', sub_eq_add_neg] at h,
rw [h.symm, (mul_comm 2 (a + -1)), mul_assoc, h.symm, add_mul_self_eq, (add_zero (a*a)).symm],
have : 0 + (2 * a * -1 + (-1) * -1) < (0 : ℤ), by 
{
  ring, 
  have := (add_le_add_iff_left (-(2 * a))).2 ha, ring at this,
  suffices h: -a < (0:ℤ), 
    exact lt_of_le_of_lt this h,
  by_contradiction, 
  rw [not_lt, le_neg] at a_1,
  exact le_trans ha a_1,
},
rw add_assoc,
have := (add_lt_add_iff_left (a*a)).2 this, rw ←add_assoc at this,
exact this,
end
 
lemma lemma_10 {p a b n : ℤ} (zero_lt_p : 0 < p) 
(ha : 2*abs a < p) (hb : 2*abs b < p) (hn_0 : 0 < n) (hn_3 : n ≤ 3) :
a^2 + n*b^2 < p^2 := begin
suffices h : 4 * (a^2 + n * b^2) < 4 * p^2,
  exact lt_of_mul_lt_mul_left h (show (4:ℤ) ≥ 0, by norm_num),
rw [(show (2:ℤ) = abs (2:ℤ), by refl), ←abs_mul] at ha,
replace ha := mul_self_lt_mul_self (abs_nonneg (2 * a)) ha,
rw [←abs_mul, abs_mul_self] at ha,
rw [(show (2:ℤ) = abs (2:ℤ), by refl), ←abs_mul] at hb,
replace hb := mul_self_lt_mul_self (abs_nonneg (2 * b)) hb,
rw [←abs_mul, abs_mul_self] at hb,
replace hb := mul_lt_mul' hn_3 hb (mul_self_nonneg (2 * b)) (show (3:ℤ) > 0, by norm_num),
have := add_lt_add ha hb, ring at this, convert this, ring,
end

theorem div_div_eq_div_mul_nonneg {a b c : ℤ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) :
a / (b * c) = (a / b) / c :=
begin
  rw eq_nat_abs_of_zero_le ha,
  rw eq_nat_abs_of_zero_le hb,
  rw eq_nat_abs_of_zero_le hc,
  rw ←int.coe_nat_mul,
  rw ←int.coe_nat_div,
  rw ←int.coe_nat_div,
  rw ←int.coe_nat_div,
  rw int.coe_nat_eq_coe_nat_iff,
  rw nat.div_div_eq_div_mul,
end


lemma lemma_11 {H : list ℤ} {k r : ℤ} (H0 : H.prod ≠ 0) (h : (cons k H).prod ∣ r) :
k ∣ r / H.prod := begin
rw prod_cons at h, cases h with t h, rw [mul_comm, ←mul_assoc] at h,
rw (int.div_eq_of_eq_mul_left H0 h),
exact dvd_mul_left _ _,
end


lemma lemma_12 {N n a b: ℤ} {H : list ℤ} (H_nonneg : 0 ≤ H.prod) (H0 : H.prod ≠ 0) (h_dvd : H.prod ∣ N) 
(h0 : 0 ≤ N) (hn : (0 : ℤ) < n) (h1 : N = a^2 + n*b^2) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) 
(h : ∀ q : ℤ, q ∈ H → (prime_int q ∧ (∃ x y : ℤ, q = x^2 + n*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)))) :
∃ c d : ℤ, N / (prod H) = c^2 + n * d^2  ∧ nat.coprime (nat_abs c) (nat_abs d):= begin
induction H with k H h2,
existsi a, existsi b,
rw [(int.div_one N).symm,
(show 1 = prod ([] : list ℤ), by {rw (prod_nil).symm,})] at h1,
exact and.intro h1 h_ab,
have : 0 < k, begin 
  have a1 := (h k (mem_cons_self k H)).2,  
  rcases a1 with ⟨x, y, this⟩, 
  have a2 := or_iff_not_imp_right.1 (lt_or_eq_of_le (nonneg_int hn this.1)),
  have := ne.symm (prime_int_ne_zero (h k (mem_cons_self k H)).1),
  unfold ne at this, exact a2 this,
end,
rw [prod_cons, mul_comm, (div_div_eq_div_mul_nonneg h0 (list.prod_cons_nonneg this H_nonneg) (int.le_of_lt this))],
have h_dvd_: prod H ∣ N, by 
{
  suffices : prod H ∣ prod (k :: H),
    exact dvd_trans this h_dvd,
  rw prod_cons, exact (dvd_mul_left _ _),
},
have h3 : ∀ (q : ℤ), q ∈ H → (prime_int q ∧ ∃ (x y : ℤ), q = x ^ 2 + n * y ^ 2 ∧ nat.coprime (nat_abs x) (nat_abs y)), by {rintro q h3, exact h q (mem_cons_of_mem k h3)},
have H0': prod H ≠ 0, by {rw prod_cons at H0, exact ne_zero_of_mul_ne_zero_left H0},
replace h2 := h2 (list.prod_cons_nonneg this H_nonneg) H0' h_dvd_ h3,
rcases h2 with ⟨a_, b_, h2⟩,
replace h3 := (h k (mem_cons_self k H)).2, rcases h3 with ⟨x, y, h3⟩,
have h4 := lemma_11 H0' h_dvd, rw h2.1 at h4, rw h2.1,
exact lemma_q_prime hn h3.1 h4 h2.2 h3.2 (h k (mem_cons_self k H)).1,
end

lemma lemma_13 {r p a b n: ℤ} (h : 0 < r) (hn : 0 < n)
(hr : a^2 + n*b^2 = p * r) (h_ab : nat.coprime (nat_abs a) (nat_abs b)): 
(∀ q ∈ (prime_int_factors r), (prime_int q ∧ ∃ c d : ℤ, q = c^2 + n * d^2 ∧ (nat.coprime (nat_abs c) (nat_abs d))))
→ ∃ x y : ℤ, p = x^2 + n * y^2 ∧ nat.coprime (nat_abs x) (nat_abs y) := begin
intro h0, 
let N := a^2 + n*b^2, have hN : N = a^2 + n*b^2, by refl, rw hN.symm at hr,
have h1 := prime_int_factors_prod h,
have h2 := prime_int_factors_ne_zero r,
have h3 := dvd.intro_left _ hr.symm, rw h1.symm at h3,
have h4 := add_le_add' (mul_self_nonneg a) ((mul_le_mul_left hn).2 (mul_self_nonneg b)),
ring at h4, rw hN.symm at h4, 
have h5 := prime_int_factors_prod_nonneg r,
have := lemma_12 h5 h2 h3 h4 hn hN h_ab h0,
rw [h1, int.div_eq_of_eq_mul_left _ hr] at this,
rcases this with ⟨c, d, this⟩,
existsi c, existsi d,
exact this,
rw h1 at h2, exact h2,
end

lemma rewrite_int {r : ℤ} (hr : r ≠ 0) : ∃ (k : ℕ) (r_ : ℤ) , r = 2^(k)*r_ ∧ ¬ 2 ∣ r_ := begin
let k := padic_val 2 r,
have hk : k = padic_val 2 r, by refl,
have h := padic_val.spec (show (2:ℕ) > 1, by norm_num) hr,
rw [←hk, coe_nat_pow] at h,
have h0: r = 2 ^ k * (r / (2 ^ k)), by 
{
  have := int.mul_div_cancel_left r (int.ne_zero_of_pos (pos_int_pow_pos _ k)), 
  rw ←int.mul_div_assoc, exact this.symm, exact h, simp,
},
existsi k, existsi (r / (2 ^ k)), split, 
exact h0,
rw [←(mul_dvd_mul_iff_left (int.ne_zero_of_pos (pos_int_pow_pos (show (2:ℤ) > 0, by norm_num) k))),
int.mul_div_cancel', ←pow_succ'],
have h1 : k + 1 > padic_val 2 r, by {rw hk, apply nat.lt_succ_self},
have := padic_val.is_greatest (show 2>1, by norm_num) hr _ h1,
rw int.coe_nat_pow at this, exact this,
rw h0, simp,
end


lemma lemma_r_pos {a b n r p : ℤ} (zero_lt_p : 0 < p) (hr : a ^ 2 + n * b ^ 2 = p * r) (hn0 : 0 < n) 
(h_dvd : p ∣ a ^ 2 + n * b ^ 2 ∧ nat.coprime (nat_abs a) (nat_abs b) ∧ 
2 * abs a < p ∧ 2 * abs b < p) :
0 < r := begin
have hr0 : r ≠ 0, 
{
  unfold ne, unfold nat.coprime at h_dvd, by_contradiction h, 
  rw [h, mul_zero, pow_two, pow_two, (mul_comm n _) ] at hr,
  have := (add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg' (mul_self_nonneg a)
  ((mul_nonneg_iff_right_nonneg_of_pos hn0).2 (mul_self_nonneg b))).1 hr,
  rw [(eq_zero_of_mul_self_eq_zero this.1), nat_abs_zero, nat.gcd_zero_left] at h_dvd,
  cases (nat_abs_eq b) with h1 h1,
  rw [h1, h_dvd.2.1, (show ↑(1:ℕ) = (1:ℤ), by refl), one_mul, one_mul] at this,
  rw this.2 at hn0, exact hn0,
  rw [h1, h_dvd.2.1, (show -↑(1:ℕ) = (-1:ℤ), by refl), (show (-1) * -1 * n = n, by norm_num)] at this,
  rw this.2 at hn0, exact hn0,
},
suffices : 0 ≤ r, 
  exact lt_of_le_of_ne this (ne.symm hr0),
have := nonneg_int hn0 hr.symm, rw mul_comm at this,
exact (mul_nonneg_iff_right_nonneg_of_pos zero_lt_p).1 this,
end

lemma lemma_prime_int_odd {p n : ℤ} (hn : n = 1 ∨ n = 2) (hp : prime_int p) (zero_lt_p : 0 < p)
(h0 : ¬∃ (x y : ℤ), p = x ^ 2 + n * y ^ 2 ∧ nat.coprime (nat_abs x) (nat_abs y)):
nat_abs p ≠ 2 := begin
  unfold ne, by_contradiction,
    cases (nat_abs_eq p) with h_nat_abs,
    rw a at h_nat_abs,
    rw not_exists at h0, 
    cases hn,
    {
      replace h0 := not_exists.1 (h0 (1:ℤ)) (1:ℤ), rw hn at h0,
      rw (show (↑(2:ℕ):ℤ) = 1^2 + 1 * 1^2, by refl) at h_nat_abs,
      have : nat.coprime (nat_abs 1) (nat_abs 1), by {unfold nat.coprime, simp},
      exact absurd (and.intro h_nat_abs this) h0,
    },
    {
      replace h0 := not_exists.1 (h0 (0:ℤ)) (1:ℤ), rw hn at h0, 
      rw (show (↑(2:ℕ):ℤ) = 0^2 + 2 * 1^2, by refl) at h_nat_abs,
      have : nat.coprime (nat_abs 0) (nat_abs 1), by {unfold nat.coprime, simp},
      exact absurd (and.intro h_nat_abs this) h0,
    },
  rw [h, a] at zero_lt_p,
  exact zero_lt_p,
end

definition P (n p : ℤ) := (prime_int p ∧ nat_abs p ≠ 2) ∧ 0 < p ∧
(∃ a b : ℤ, p ∣ (a^2 + n*b^2) ∧ (nat.coprime (nat_abs a) (nat_abs b))) ∧
¬(∃ x y : ℤ, p = x^2 + n*y^2 ∧ (nat.coprime (nat_abs x) (nat_abs y)))

lemma descent_12 {n : ℤ} (hn : n = 1 ∨ n = 2) :
∀ p : ℤ, P n p → ∃ q : ℤ, P n q ∧ q < p := begin
intros p hp, rcases hp with ⟨hp, zero_lt_p, h_dvd, h0⟩,
rcases h_dvd with ⟨a, b, h_dvd⟩,
have hn0 : 0 < n, by {cases hn, rw hn, norm_num, rw hn, norm_num},
have hn3 : n ≤ 3, by {cases hn, rw hn, norm_num, rw hn, norm_num},
replace h_dvd := lemma_8 hn0 zero_lt_p hp h_dvd.1 h_dvd.2,
rcases h_dvd with ⟨a_, b_, h_dvd⟩, 
cases h_dvd.1 with r hr,
have hrlt0 := lemma_r_pos zero_lt_p hr hn0 h_dvd,
let H := prime_int_factors r, let N := a_^2 + n*b_^2, 
have hN : N = a_^2 + n*b_^2, by refl,
have Hr : prod H = r, by {rw (prime_int_factors_prod hrlt0).symm},
have Hnonneg:= prime_int_factors_prod_nonneg r,
have H_dvd := (dvd.intro_left p hr.symm), rw [Hr.symm, hN.symm] at H_dvd,
have h2 := lemma_13 hrlt0 hn0 hr h_dvd.2.1,
have h := not.imp h0 h2,
rw not_forall at h, cases h with q h, 
rw [not_imp, not_and_distrib, or_iff_not_imp_left] at h,
existsi q, split, split,
have hq2 := lemma_prime_int_odd hn (prime_int_mem_factors h.1) (prime_int_factors_mem_pos h.1) 
(h.2 (not_not.2 (prime_int_mem_factors h.1))),
exact and.intro (prime_int_mem_factors h.1) hq2, split,
exact prime_int_factors_mem_pos h.1, split,
have := dvd_prod h.1,
rw (show prime_int_factors r = H, by refl) at this,
rw hN at H_dvd,
existsi a_, existsi b_,
exact and.intro (dvd_trans this H_dvd) h_dvd.2.1,
exact h.2 (not_not.2 (prime_int_mem_factors h.1)),
suffices a : r < p, 
  have := prime_int_factors_mem_le_prod hrlt0 h.1,
  exact lt_of_le_of_lt this a,
have h1:= lemma_10 zero_lt_p h_dvd.2.2.1 h_dvd.2.2.2 hn0 hn3,
rw [hr, pow_two, mul_lt_mul_left zero_lt_p] at h1,
exact h1,
end 

lemma lemma_14 {a b: ℤ} {H : list ℤ} (h_dvd : H.prod ∣ a^2 + 3 * b^2) 
(h0 : 0 ≤ a^2 + 3 * b^2) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) 
(h : ∀ q : ℤ, q ∈ H → q = (4:ℤ)) :
∃ c d : ℤ, (a^2 + 3 * b^2) / (prod H) = c^2 + 3 * d^2  ∧ nat.coprime (nat_abs c) (nat_abs d):= begin
induction H with k H h2,
{
  existsi a, existsi b, 
  rw [prod_nil, int.div_one], 
  split, refl, exact h_ab,
},
have hk4 := (h k (mem_cons_self k H)), 
have h_dvd_: prod H ∣ a^2 + 3 * b^2, by 
{
  suffices : prod H ∣ prod (k :: H),
    exact dvd_trans this h_dvd,
  rw prod_cons, exact (dvd_mul_left _ _),
},
have qnonneg: ∀ q : ℤ, q ∈ H → 0 ≤ q, by 
{
  intros q a, have := h q (mem_cons_of_mem k a), rw this, norm_num,
},
rw [prod_cons, mul_comm k _, (div_div_eq_div_mul_nonneg h0 (list.prod_nonneg_of_mem_nonneg qnonneg) (show 0 ≤ k, by {rw hk4, norm_num}))],
have hq4 : (∀ (q : ℤ), q ∈ H → q = 4), by {intros q a, exact h q (mem_cons_of_mem k a)},
replace h2 := h2 h_dvd_ hq4, 
rcases h2 with ⟨c, d, h2⟩, rw h2.1,
have qnezero : ∀ q : ℤ, q ∈ H → q ≠ 0, by {intros q a, rw hq4 q a, norm_num},
have H0 := list.prod_ne_zero _ _ _ qnezero,
have h3 := lemma_11 H0 h_dvd, rw [h2.1, hk4] at h3, rw hk4,
have := lemma_q_4_n_3 (show (4:ℤ) = 1^2 + 3*1^2, by refl) _ h3 h2.2 _,
exact this, exact nat.coprime_one_right (nat_abs 1), simp,
intros x y, exact mul_eq_zero.1, simp,
end

lemma nat.mod_eq_mod_iff_mod_sub_eq_zero {m n k : ℕ} (h : k ≤ m) : 
m % n = k % n ↔ (m - k) % n = 0 := begin
rw [←nat.dvd_iff_mod_eq_zero, ←coe_nat_dvd, (int.coe_nat_sub h), 
←nat.modeq.modeq_iff_dvd],
unfold nat.modeq, split, 
intro h0, rw h0, intro h0, rw h0,
end

lemma lemma_15 {k : ℕ} {p a b : ℤ} (h : a^2 + 3*b^2 = p * 2^k)
(h_ab : nat.coprime (nat_abs a) (nat_abs b)) (h_2dvd : ¬ 2 ∣ p) (hp : p ≠ 0) (hk1 : 1 ≤ k):
k % (2:ℕ) = 0 := begin
cases nat.mod_two_eq_zero_or_one k with hk hk,
exact hk,
exfalso, 
rw [(show (1:ℕ) = 1 % 2, by refl), (show bit0 (1 % 2) = 2, by refl),
nat.mod_eq_mod_iff_mod_sub_eq_zero hk1, ←nat.dvd_iff_mod_eq_zero] at hk,
rcases hk with ⟨l, hk⟩, rw (nat.sub_eq_iff_eq_add hk1) at hk,
rw [hk, pow_add, pow_mul, (show p * ((2 ^ 2) ^ l * 2 ^ 1) = p * 2 * 4^l, by ring), 
(prod_repeat (4:ℤ) l).symm] at h, 
have h1 : (∀ (q : ℤ), q ∈ repeat (4:ℤ) l → q = 4), {intros q h1, exact eq_of_mem_repeat h1},
have h0:= lemma_14 (dvd.intro_left _ h.symm) (nonneg_int _ (eq.refl (a^2+ 3 * b^2))) h_ab h1,
rcases h0 with ⟨c, d, h0⟩,
rw (int.div_eq_of_eq_mul_left _ h) at h0,
have := four_dvd_of_two_dvd h0.2 (dvd.intro_left _ h0.1),
rw [h0.1.symm, (show (4:ℤ) = 2 * 2, by refl), mul_dvd_mul_iff_right _] at this,
exact absurd this h_2dvd,
simp, norm_num, 
rw prod_repeat,
exact int.ne_zero_of_pos (pos_int_pow_pos (show (0:ℤ) < 4, by norm_num) l),
norm_num, 
end

lemma descent_for_p_2 {k : ℕ} {p a b: ℤ} (h : a^2 + 3*b^2 = p * 2^k)
(h_ab : nat.coprime (nat_abs a) (nat_abs b)) (h_2dvd : ¬ 2 ∣ p) (hp : p ≠ 0) : 
∃ x y : ℤ, (a^2 + 3*b^2)/(2^k) = x^2 + 3*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y):= begin
cases (dec_em (k = 0)) with hk0 hk0,
rw hk0, 
existsi a, existsi b, split, simp, exact h_ab,
have hk := lemma_15 h h_ab h_2dvd hp _,
rw [←nat.dvd_iff_mod_eq_zero] at hk,
cases hk with l hk,
rw [hk, pow_mul, (show (2:ℤ)^2 = 4, by refl), (prod_repeat (4:ℤ) l).symm] at h,
have h1 : (∀ (q : ℤ), q ∈ repeat (4:ℤ) l → q = 4), {intros q h1, exact eq_of_mem_repeat h1},
have := lemma_14 (dvd.intro_left _ h.symm) _ h_ab h1,
rw (show prod (repeat (4:ℤ) l) = 2 ^ k, by {rw [prod_repeat, hk, pow_mul], norm_num}) at this,
exact this,
exact nonneg_int (show (0:ℤ) < 3, by norm_num) (eq.refl (a^2 + 3 * b^2)),
exact nat.pos_iff_ne_zero.2 hk0,
end

lemma descent_3 : ∀ p : ℤ, P 3 p → ∃ q : ℤ, P 3 q ∧ q < p := begin
intros p h, 
have hn0 : (0:ℤ) < 3, by norm_num,
rcases h with ⟨hp, zero_lt_p, h_dvd, h0⟩,
rcases h_dvd with ⟨a, b, h_dvd⟩,
replace h_dvd := lemma_8 hn0 zero_lt_p hp h_dvd.1 h_dvd.2,
rcases h_dvd with ⟨a_, b_, h_dvd⟩,
cases h_dvd.1 with r' hr',
have r'nonzero : r' ≠ 0, 
{
  unfold ne, by_contradiction h0,
  rw [h0, mul_zero, 
  add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg',
  pow_two, pow_two] at hr', 
  unfold nat.coprime at h_dvd,
  rw [(eq_zero_of_mul_self_eq_zero hr'.1), nat_abs_zero, nat.gcd_zero_left,
  ←nat.mul_self_inj, ←int.coe_nat_eq_coe_nat_iff, nat_abs_mul_self] at h_dvd,
  rw h_dvd.2.1 at hr', norm_num at hr', exact hr',
  rw pow_two, apply mul_self_nonneg,
  rw [(mul_zero (3:ℤ)).symm, mul_le_mul_left, pow_two],
  apply mul_self_nonneg,
  simp,
},
rcases (rewrite_int r'nonzero) with ⟨k, r, hr⟩,
rw [hr.1, mul_comm _ r, ←mul_assoc] at hr', 
have two_dvd : ¬ 2 ∣ p * r, 
{
  by_contradiction a,
  rw (prime_int_dvd_mul prime_int_two) at a,
  cases a with a a,
  exact absurd a (not_two_dvd_odd_prime_int hp),
  exact absurd a hr.2,
},
have ne_zero : p * r ≠ 0, 
{
  unfold ne, by_contradiction a, rw a at two_dvd, exact absurd (dvd_zero 2) two_dvd,
},
replace h := descent_for_p_2 hr' h_dvd.2.1 two_dvd ne_zero,
rw (int.div_eq_of_eq_mul_left (pow_ne_zero' (show (2:ℤ) ≠ 0, by norm_num)) hr') at h,
rcases h with ⟨a', b', h⟩,
have h0ltr : 0 < r, 
{
  suffices h1 : 0 < p * r,
    rw [←(mul_lt_mul_left zero_lt_p), mul_zero],
    exact h1,
  rw lt_iff_le_and_ne,
  exact and.intro (nonneg_int hn0 h.1) (ne.symm ne_zero),
},
have h1 := lemma_13 h0ltr hn0 h.1.symm h.2,
replace h1 := not.imp h0 h1,
rw not_forall at h1, 
cases h1 with q h1,
rw [not_imp, not_and] at h1,
existsi q, split, split,
have : nat_abs q ≠ 2, 
{
  unfold ne, by_contradiction a0,
  have h2 := dvd_mul_of_dvd_right (dvd_prod h1.1) p,
  rw [←nat_abs_dvd, prime_int_factors_prod h0ltr, a0] at h2,
  exact absurd h2 two_dvd,
},
exact and.intro (prime_int_mem_factors h1.1) this, split,
exact prime_int_factors_mem_pos h1.1, split,
existsi a_, existsi b_,
have := prime_int_factors_prod h0ltr,
rw [mul_comm p r, this.symm, mul_assoc] at hr',
exact and.intro (dvd.trans (dvd_prod h1.1) (dvd.intro _ hr'.symm)) h_dvd.2.1,
exact h1.2 (prime_int_mem_factors h1.1),
suffices a : r < p, 
  have := prime_int_factors_mem_le_prod h0ltr h1.1,
  exact lt_of_le_of_lt this a,
have h2 := lemma_10 zero_lt_p h_dvd.2.2.1 h_dvd.2.2.2 hn0 _,
rw [hr', pow_two, mul_assoc, mul_lt_mul_left zero_lt_p] at h2,
suffices : r ≤ r * 2^k,
  exact lt_of_le_of_lt this h2,
rw (le_mul_iff_one_le_right h0ltr),
exact pos_int_pow_pos (show (0:ℤ) < 2, by norm_num) k, norm_num,
end

lemma lemma_16 {n : ℤ} (hn : n = 1 ∨ n = 2 ∨ n = 3) : 
∀ p : ℤ, (p > 0 ∧ P n p) → ∃ q : ℤ, q > 0 ∧ P n q ∧ q < p := begin
intros p h0,
rw ←or_assoc at hn, cases hn with hn hn,
have h := descent_12 hn p h0.2, cases h with q h,
existsi q,
split,
exact h.1.2.1, exact h,
rw hn at h0, rw hn,
have h := descent_3 p h0.2, cases h with q h,
existsi q, 
split, exact h.1.2.1, exact h,
end


lemma posint_well_founded (q : ℤ → Prop) [decidable_pred q] (h : ∀ n : ℤ, (n > 0 ∧ q n) → ∃ r : ℤ, r > 0 ∧ q r ∧ r < n) :
¬ (∃ a : ℤ, a > 0 ∧ q a) := begin
  intro H,
  cases H with a Ha,
  have H : ∃ b : ℕ, b > 0 ∧ q b,
    existsi int.nat_abs a,
    split,
      show 0 < int.nat_abs a,
      rw ←int.coe_nat_lt_coe_nat_iff,
      show (0 : ℤ) < int.of_nat _,
      rw int.of_nat_nat_abs_eq_of_nonneg (int.le_of_lt Ha.1),
      exact Ha.1,
    show q (int.of_nat _),
    rw int.of_nat_nat_abs_eq_of_nonneg (int.le_of_lt Ha.1),
    exact Ha.2,
  let c := nat.find H,
  have Hc : (c : ℤ) > 0,
    show ((0 : ℕ) : ℤ) < c,
    rw int.coe_nat_lt,
    exact (nat.find_spec H).1,
  have Hr := h c ⟨Hc,(nat.find_spec H).2⟩,
  cases Hr with r Hr,
  let s := int.nat_abs r,
  have Hs : (s : ℤ) = r,
    show int.of_nat (int.nat_abs r) = r,
    rw int.of_nat_nat_abs_eq_of_nonneg,
    exact int.le_of_lt Hr.1,
  have H1 : s < c,
    rw ←int.coe_nat_lt,
    rw Hs,
    exact Hr.2.2,
  apply nat.find_min H H1,
  split,
    show 0 < s,
    rw ←int.coe_nat_lt,
    rw Hs,
    exact Hr.1,
  rw Hs,
  exact Hr.2.1
end

lemma descent_step_123 {p n : ℤ} (hn : n = 1 ∨ n = 2 ∨ n = 3) (hp : prime_int p ∧ nat_abs p ≠ (2:ℕ)) (zero_lt_p : (0:ℤ) < p):
(∃ a b : ℤ, p ∣ (a^2 + n*b^2) ∧ (nat.coprime (nat_abs a) (nat_abs b))) → (∃ x y : ℤ, p = x^2 + n * y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) := 
begin
intro h,
by_contradiction h0, 
have h1 := posint_well_founded (P n) (lemma_16 hn),
have : p > 0 ∧ P n p, by 
{
  split, exact zero_lt_p, 
  unfold P, split,
  exact hp, split,
  exact zero_lt_p, split,
  exact h, exact h0,
},
rw not_exists at h1,
exact absurd this (h1 p),
end

------------ lemmas for reciprocity step ------------------


lemma lemma_17 {n p: ℤ} (h_n : n ≠ 0) (hp : prime_int p ∧ nat_abs p ≠ 2) (h_dvd : ¬ p ∣ n ) (zero_le_p : 0 ≤ p): 
(∃  x y : ℤ, p ∣ x^2 + n*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) ↔ legendre_sym (-n) hp = 1 := 
begin
have h0 := eq_nat_abs_of_zero_le zero_le_p,
split, 
{
  intro h, 
  rcases h with ⟨x, y, h⟩,
  rw ←modeq.modeq_zero_iff at h,
  have H : quadratic_res (-n) p, 
  {
    -- have h1 := modeq.modeq_sub h.1 (modeq.refl (n*y^2)),
    -- rw [pow_two, pow_two, add_sub_cancel, sub_eq_add_neg, zero_add, h0, 
    -- ←(zmodp.eq_iff_modeq_int hp.1), neg_mul_eq_neg_mul, cast_mul (-n) _] at h1,
    -- replace h1 := eq_div_of_mul_eq _ _ _ h1.symm,
    -- have h2 := zmodp.mul_inv_eq_gcd hp.1 (nat_abs y),
    -- have h3 : (↑(nat_abs y) : zmodp _ hp.1) = (↑(↑(nat_abs y) : ℤ) : zmodp _ hp.1), by refl,
    -- rw [h3, mul_comm, ←div_eq_iff_mul_eq] at h2,
    -- have : (↑x * (↑↑(nat_abs y))⁻¹ : zmodp _ hp.1) = (↑↑(nat_abs y))⁻¹ * ↑x, by {rw mul_comm},
    -- rw [division_def, ←(@nat_abs_mul_self y), int.coe_nat_mul, cast_mul, cast_mul, (inv_div_left _ _).symm, div_eq_mul_inv,
    -- h2.symm] at h1,
    sorry,
  },
  unfold legendre_sym, split_ifs with a1 a2, 
  simp,
  rw not_and_not_right at a1,
  exact absurd ((dvd_neg p n).1 (a1 H)) h_dvd,
},
{
  intro h, unfold legendre_sym at h, split_ifs at h,
  unfold quadratic_res at h_1,
  cases h_1.1 with x hx,
  rw [h0.symm, modeq.modeq_iff_dvd, (show x^2 - -n = x^2 + n*1^2, by ring)] at hx, 
  existsi x, existsi (1:ℤ),
  rw (show nat_abs 1 = 1, by norm_num),
  exact and.intro hx (nat.coprime_one_right (nat_abs x)),
  exfalso, norm_num at h, exfalso, norm_num at h,
},
end

lemma nat_abs_mod (a : ℤ) : a % 2 = (((nat_abs a) % 2) : ℕ) :=
begin
  cases nat_abs_eq a,
    rw int.coe_nat_mod,
    rw ←h,
    refl,
  rw int.coe_nat_mod,
  replace h := eq_neg_of_eq_neg h,
  rw h,
  clear h,
  show a % 2 = (-a) % 2,
  rw mod_eq_mod_iff_mod_sub_eq_zero,
  rw sub_neg_eq_add,
  rw ←mul_two,
  rw mul_mod_left,
end

lemma neg_one_pow_even {a : ℤ} : (-1:ℤ)^(nat_abs (a:ℤ)) = (1:ℤ) ↔ a % 2 = 0 := 
begin
rw nat_abs_mod, let b := nat_abs a, 
conv  begin to_lhs, rw ←nat.mod_add_div (nat_abs a) 2, end,
rw [add_comm, pow_add, pow_mul, (show (-1:ℤ)^2 = 1, by refl), one_pow, one_mul], 
have := nat.mod_two_eq_zero_or_one (nat_abs a), cases this, rw this, 
simp, rw this, exact dec_trivial,
end

lemma neg_one_pow_odd {a : ℤ} : (-1:ℤ)^(nat_abs (a:ℤ)) = (-1:ℤ) ↔ a % 2 = 1 := begin
have h1 : a % 2 = 1 ↔ ¬  a % 2 = 0, 
{ 
  have := int.mod_two_eq_zero_or_one a, 
  cases this, rw this, simp, rw this, simp,
},
have h2 : (-1:ℤ)^(nat_abs a) = (-1:ℤ) ↔ ¬ (-1:ℤ)^(nat_abs a) = (1:ℤ),
{
  have := neg_one_pow_eq_or (nat_abs a), 
  cases this, rw this, norm_num, rw this, norm_num,
},
rw [h1, h2, neg_one_pow_even],
end

-- lemma zmod_eq_iff_lt {a b n : ℤ} (ha_0 : 0 ≤ a) (ha : a < n) (hb_0 : 0 ≤ b) (hb : b < n) :
-- a ≡ b [ZMOD n] ↔ a = b := begin
-- conv in (a = b) begin
-- rw [(mod_eq_of_lt ha_0 ha).symm, (mod_eq_of_lt hb_0 hb).symm],
-- end,
-- unfold modeq,
-- end

lemma reciprocity_step_1 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_lt_p : 0 < p): 
p ≡ 1 [ZMOD 4] → ∃ a b : ℤ, (p ∣ (a^2 + 1*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := begin
have h_dvd : ¬ p ∣ 1, 
{
  by_contradiction, 
  have := eq_one_of_dvd_one (int.le_of_lt zero_lt_p) a, 
  rw this at hp, 
  exact absurd hp.1 nat.not_prime_one,
},
intro h, rw (lemma_17 (show (1:ℤ) ≠ 0, by norm_num) hp h_dvd (int.le_of_lt zero_lt_p)),
rw [(LQR_supplementary_1 hp (int.le_of_lt zero_lt_p)), neg_one_pow_even, ←dvd_iff_mod_eq_zero],
replace h := modeq.symm h, 
rw [modeq.modeq_iff_dvd] at h, cases h with k hk,
rw (show 4 * k = 2 * (2*k), by ring) at hk,
unfold has_dvd.dvd, existsi k, rw [hk], 
exact int.mul_div_cancel_left (2*k) (show (2:ℤ) ≠ (0:ℤ), by norm_num),
end

lemma reciprocity_step_2 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_lt_p : 0 < p): 
((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) → ∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := begin
have h_dvd : ¬ p ∣ 2, 
{
  by_contradiction, 
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at a,
  cases prime_int_two.2 (nat_abs p) a,
  unfold prime_int at hp, rw h at hp,
  exact absurd hp.1 (nat.not_prime_one),
  rw h at hp, 
  exact absurd (show nat_abs 2 = (2:ℕ), by refl) hp.2,
},
intro h, rw (lemma_17 (show (2:ℤ) ≠ 0, by norm_num) hp h_dvd (int.le_of_lt zero_lt_p)),
rw [(neg_one_mul (2:ℤ)).symm, legendre_sym_mul,
(LQR_supplementary_2 hp), (LQR_supplementary_1 hp (int.le_of_lt zero_lt_p))],
cases h,
{
  have h_p8: p % 8 = (1:ℤ), {unfold modeq at h, exact h},
  have h1 := quad_res_two_int p (or.intro_left (p % 8 = (7:ℤ)) h_p8),
  replace h := modeq.symm h,
  rw [modeq.modeq_iff_dvd] at h, cases h with k h,
  rw [(neg_one_pow_even.2 h1), mul_one, neg_one_pow_even,
  mod_eq_zero_of_dvd],
  unfold has_dvd.dvd, existsi (2*k),
  rw h, rw (show 8 * k / 2 = 2 * (2 * (2 * k)) / 2, by ring),
  rw (int.mul_div_cancel_left _ (show (2:ℤ) ≠ 0, from dec_trivial)) 
},
{
  have h_p8:  p % 8 = (3:ℤ), {unfold modeq at h, exact h},
  have h1 := quad_nonres_two_int p (or.intro_left (p % 8 = (5:ℤ)) h_p8),
  replace h := modeq.symm h,
  rw [modeq.modeq_iff_dvd] at h, cases h with k h,
  rw sub_eq_iff_eq_add at h, 
  rw [(neg_one_pow_odd.2 h1), mul_neg_one, ←neg_eq, neg_one_pow_odd, 
  (show (1:ℤ) = 1%2, by refl), (show bit0 (1 % 2) = (2:ℤ), by refl), 
  mod_eq_mod_iff_mod_sub_eq_zero, mod_eq_zero_of_dvd],
  conv in (p-1%2) begin rw (show (1:ℤ) % 2 = (1:ℤ), by refl), end,
  unfold has_dvd.dvd, 
  existsi (2*k),
  rw h,
  conv in ((8 * k + 3 - 1) / 2) begin
    rw [(show (8 * k + 3 - 1) / 2 = 2* (4 * k + 1) / 2, by ring), 
    (int.mul_div_cancel_left (4 * k + 1) (show (2:ℤ) ≠ 0, from dec_trivial))],
  end,
  ring,
},
end

lemma reciprocity_step_3 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2)  (zero_lt_p : 0 < p): 
((p = 3) ∨ (p ≡ 1 [ZMOD 3])) → ∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := begin
intro h, cases h,
{
  existsi (0:ℤ), existsi (1:ℤ),
  exact and.intro (show p ∣ 0 ^ 2 + 3 * 1 ^ 2, by {ring, rw h})
  (nat.coprime_one_right (nat_abs 0)),
},
have h_dvd : ¬ p ∣ 3, 
{
  by_contradiction h0, 
  have h0_ := h0,
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at h0,
  cases prime_int_three.2 (nat_abs p) h0 with h,
  unfold prime_int at hp, rw h at hp,
  exact absurd hp.1 (nat.not_prime_one),
  have h1 : 3 ∣ p,
  {
    suffices : (nat_abs 3) ∣ (nat_abs p),
      rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd], exact this,
    rw h_1,
  },
  have := modeq.trans h.symm (modeq.modeq_zero_iff.2 (h1)), 
  rw [modeq.modeq_zero_iff] at this,
  have := eq_one_of_dvd_one (show (3:ℤ) ≥ 0, from dec_trivial) this,
  norm_num at this,
},
rw (lemma_17 (show (3:ℤ) ≠ 0, by norm_num) hp h_dvd (int.le_of_lt zero_lt_p)),
rw [(neg_one_mul (3:ℤ)).symm, legendre_sym_mul, (LQR_supplementary_1 hp (int.le_of_lt zero_lt_p))],
have h3: prime_int (3:ℤ) ∧ (int.nat_abs (3:ℤ)) ≠ 2, by
{split,exact prime_int_three, rw (show nat_abs (3:ℤ) = (3:ℕ), by ring), norm_num},
rw (law_of_quadratic_reciprocity' h3 hp),
have h1 : legendre_sym p h3 = 1, by
{
  unfold legendre_sym, split_ifs, refl,

  exfalso,
  rw not_and at h_1, replace h_1 := not_not.1 (h_1 h_2),
  rw [←dvd_nat_abs, ←nat_abs_dvd, coe_nat_dvd] at h_1,
  cases (hp.1.2 (nat_abs (3:ℤ)) h_1) with h1,
  rw (show (nat_abs (3:ℤ)) = (3:ℕ), by refl) at h1, norm_num at h1,
  have h2: nat_abs p ∣ nat_abs 3, {rw h_3},
  rw [←coe_nat_dvd, dvd_nat_abs, nat_abs_dvd] at h2,
  exact absurd h2 h_dvd,

  exfalso, unfold quadratic_res at h_2,
  rw [(show (3:ℤ) = ↑(nat_abs (3:ℤ)), by refl), (show (1:ℤ) = 1^2, by refl)] at h,
  rw not_exists at h_2,
  exact absurd h (h_2 (1:ℤ)),
},
rw [h1, one_mul, (pow_add (-1:ℤ) _ _).symm, 
(show (3-1)/2 = (1:ℤ), by refl), one_mul, (two_mul _).symm], 
conv in (2:ℕ) begin rw (show 2 = nat_abs (2:ℤ), by ring) end, 
rw [←nat_abs_mul, neg_one_pow_even, mod_eq_zero_of_dvd],
exact (dvd_mul_right 2 _),
end


--------------- lemmas for theorems 1 2 and 3 ----------------


theorem squares_in_mod_3 (d : ℤ) : d * d ≡ 0 [ZMOD 3] ∨ d * d ≡ 1 [ZMOD 3] := begin
have : ∀ d : zmod 3, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ), from dec_trivial,
by have := this d;
  rwa [← cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this,
end

theorem squares_in_mod_4 (d : ℤ) : d * d ≡ 0 [ZMOD 4] ∨ d * d ≡ 1 [ZMOD 4] := begin
have : ∀ d : zmod 4, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ), from dec_trivial,
by have := this d;
  rwa [← cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this,
end

theorem squares_in_mod_8 (d : ℤ) : d * d ≡ 0 [ZMOD 8] ∨ d * d ≡ 1 [ZMOD 8] ∨ d * d ≡ 4 [ZMOD 8] := begin
have : ∀ d : zmod 8, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ) ∨ d * d = (4 : ℤ), from dec_trivial,
by have := this d;
  rwa [← cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this,
end

lemma lemma_18 {p n : ℤ} (hp : prime_int p) (hpp : 0 < p) (hn : (2:ℤ) ≤ n) (hpn : ¬ p = n) : 
p ≡ 0 [ZMOD n] → false := begin
intro h,
rw [modeq.modeq_zero_iff, ←dvd_nat_abs, ←nat_abs_dvd, coe_nat_dvd] at h,
have := hp.2 (nat_abs n) h,
cases this,
cases (nat_abs_eq n),
rw [h_1, this] at hn, exact hn,
rw [h_1, this] at hn, exact hn,
have h_nat_abs_p : ↑ (nat_abs p) = p, by {apply of_nat_nat_abs_eq_of_nonneg, exact int.le_of_lt hpp},
rw [←int.coe_nat_eq_coe_nat_iff, h_nat_abs_p] at this, 
rw this.symm at hpn,
cases (nat_abs_eq n) with h0 h0,
exact absurd h0.symm hpn,
suffices h1 : n ≤ 0,
  exact le_trans hn h1, 
rw [h0, neg_nonpos, ←int.coe_nat_zero, int.coe_nat_le], 
exact dec_trivial,
end

lemma lemma_19 {p a n : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (ha : (2:ℤ) ∣ a) (hn : (2:ℤ) ∣ n) :
p ≡ a [ZMOD n] → false := begin
intro h,
rcases ha with k,
have := modeq.modeq_of_dvd_of_modeq hn h,
rw [modeq.modeq_iff_dvd, ←dvd_neg, ha_h] at this, 
replace this := mod_eq_zero_of_dvd this,
rw [(show -(2 * k - p) = p + 2 * (-k), by ring), (add_mul_mod_self_left p 2 (-k))] at this,
have h1:= eq.trans (odd_prime_int_is_odd hp).symm this, 
simp at h1, exact h1,
end

----------------------

theorem Thm_1 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_lt_p : 0 < p):
(∃ x y : ℤ, p = x^2 + y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) ↔ p ≡ 1 [ZMOD 4] := 
begin
split, 
rintro ⟨x, y, h1⟩, 
have h_4 : ¬ p = 4,
{
  by_contradiction, rw a at hp, unfold prime_int at hp, 
  exact absurd hp.1 (show ¬ nat.prime 4, by norm_num),
},
have h_x := squares_in_mod_4 x, ring at h_x,
have h_y := squares_in_mod_4 y, ring at h_y,
cases h_x, cases h_y, 

exfalso,
have h := modeq.modeq_add h_x h_y,
rw h1.1.symm at h,
exact lemma_18 hp.1 zero_lt_p (show (2:ℤ) ≤ (4:ℤ), by norm_num) h_4 h,

have h := modeq.modeq_add h_x h_y,
rw h1.1.symm at h, exact h,

cases h_y,
have h := modeq.modeq_add h_x h_y,
rw h1.1.symm at h,
exact h,

exfalso,
have h := modeq.modeq_add h_x h_y,
rw h1.1.symm at h, 
exact lemma_19 hp (show (2:ℤ)∣ (1:ℤ) + (1:ℤ), by refl) (show (2:ℤ) ∣ (4:ℤ), from ⟨(2:ℤ),rfl⟩) h,

intro ha, 
have hn : (1:ℤ) = 1 ∨ (1:ℤ) = 2 ∨ (1:ℤ) = 3, by simp,
have := descent_step_123 hn hp zero_lt_p (reciprocity_step_1 hp zero_lt_p ha),
rcases this with ⟨x, y, this⟩, rw one_mul at this,
existsi x, existsi y, exact this,
end

theorem Thm_2 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_lt_p : 0 < p):
(∃ x y : ℤ, p = x^2 + 2*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) ↔ ((p ≡ 1 [ZMOD (8:ℤ)]) ∨ (p ≡ 3 [ZMOD (8:ℤ)])) := 
begin split, intro h,

have h_8 : ¬ p = (8:ℤ), begin
  by_contradiction, rw a at hp, unfold prime_int at hp,
  have : ¬ nat.prime (8:ℕ), by norm_num,
  exact absurd hp.1 this,
end,
rcases h with ⟨x, y, h0⟩,
have h_x := squares_in_mod_8 x, ring at h_x,
have h_y := squares_in_mod_8 y, ring at h_y,
cases h_x, cases h_y, 

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h,
exact lemma_18 hp.1 zero_lt_p (show (2:ℤ) ≤ (8:ℤ), by norm_num) h_8 h,

cases h_y,
exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_19 hp (show (2:ℤ)∣ (0:ℤ) + (2:ℤ) * (1:ℤ), by simp) (show (2:ℤ)∣(8:ℤ), from ⟨(4:ℤ), rfl⟩) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
replace h_y := modeq.trans h_y (show 2*4 ≡ 0 [ZMOD (8:ℤ)], by refl),
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h,
exact lemma_18 hp.1 zero_lt_p (show (2:ℤ) ≤ (8:ℤ), from dec_trivial) h_8 h,

cases h_y, cases h_x,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h,
exact or.intro_left (p ≡ 3 [ZMOD (8:ℤ)]) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_19 hp (show 2∣ (4:ℤ) + (2:ℤ) * (0:ℤ), from ⟨(2:ℤ), rfl⟩) (show 2∣(8:ℤ), from ⟨(4:ℤ), rfl⟩) h,

cases h_x, cases h_y, 
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact or.intro_right (p ≡ 1 [ZMOD (8:ℤ)]) h,

replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact or.intro_left (p ≡ 3 [ZMOD (8:ℤ)]) h,

cases h_y,
exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_19 hp (show 2∣ (4:ℤ) + (2:ℤ) * (1:ℤ), from ⟨(3:ℤ), rfl⟩) (show 2∣(8:ℤ), from ⟨(4:ℤ), rfl⟩) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_19 hp (show 2∣ (4:ℤ) + (2:ℤ) * (4:ℤ), from ⟨(6:ℤ), rfl⟩) (show 2∣(8:ℤ), from ⟨(4:ℤ), rfl⟩) h,

intro ha, 
have hn : (2:ℤ) = 1 ∨ (2:ℤ) = 2 ∨ (2:ℤ) = 3, by simp,
exact descent_step_123 hn hp zero_lt_p (reciprocity_step_2 hp zero_lt_p ha),
end

theorem Thm_3 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_lt_p : 0 < p):
(∃ x y : ℤ, p = x^2 + 3*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) ↔ ((p = 3) ∨ (p ≡ 1 [ZMOD 3])) := begin
split, intro ha, 
unfold has_pow.pow at ha, unfold monoid.pow at ha,
have h1 := dec_em (p = 3), cases h1,
exact or.intro_left (p ≡ 1 [ZMOD 3]) h1, 
rcases ha with ⟨x, h⟩, rcases h with ⟨y, h0⟩,
rw [mul_one, mul_one] at h0,

have h_x := squares_in_mod_3 x,
have h_y := squares_in_mod_3 y,
cases h_x, cases h_y,

exfalso,
replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_18 hp.1 zero_lt_p (show (2:ℤ)≤(3:ℤ), by norm_num) h1 h,

exfalso,
replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact lemma_18 hp.1 zero_lt_p (show (2:ℤ)≤(3:ℤ), by norm_num) h1 h,

cases h_y,
replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact or.intro_right (p = 3) h,

replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h0.1.symm at h, 
exact or.intro_right (p = 3) h,

intro ha, 
have hn : (3:ℤ) = 1 ∨ (3:ℤ) = 2 ∨ (3:ℤ) = 3, by simp,
exact descent_step_123 hn hp zero_lt_p (reciprocity_step_3 hp zero_lt_p ha),
end
