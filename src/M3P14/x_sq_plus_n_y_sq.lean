import data.int.basic
import data.int.modeq
import data.int.order
import algebra.group_power
import tactic.ring
import chris_hughes_various.zmod
import M3P14.lqr

open nat 


lemma int_add_sub_l {a b c : ℤ} : a + b = c ↔ a = c - b := 
begin split, intro, rw a_1.symm, simp, intro, rw a_1, simp end
lemma int_add_sub_r {a b c : ℤ} : a = b + c ↔ a - c = b := 
begin split, intro, rw a_1, simp, intro, rw a_1.symm, simp end
lemma int_add_sub_l' {a b c : ℤ} : a + b = c ↔ b = c - a := 
begin split, intro, rw a_1.symm, ring, intro, rw a_1, ring, end
lemma int_add_sub_r' {a b c : ℤ} : a = b + c ↔ a - b = c := 
begin split, intro, rw a_1, ring, intro, rw a_1.symm, ring, end
lemma int_add_sub_three_l {a b c d : ℤ} : a = b + c + d ↔ a - b = c + d :=
begin split, intro, rw a_1, ring, intro, rw [(show b + c + d = b +(c + d), by ring), a_1.symm], ring end

lemma identity (c d n x y : ℤ) : (c^2 + n*d^2)*(x^2 + n*y^2) = (c*x - n*d*y)^2 + n*(c*y + d*x)^2 := by ring

#check int.div_le_div

lemma lemma_xy {q n x y : ℤ} (h_q : q = x^2 + n*y^2) (hq : q = 4 ∧ n = 3) (h_xy : coprime (int.nat_abs x) (int.nat_abs y)): 
(x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := 
begin
split, cases (dec_em (x = 1)), exact or.intro_left (x = -1) h,
rw [hq.1, hq.2] at h_q,
have : y ≠ 0,
begin
    by_contradiction, unfold coprime at h_xy, simp at a, rw a at h_xy, simp at h_xy, 
    have := int.nat_abs_eq x, rw h_xy at this, simp at this,
    rw or_iff_not_imp_left at this,
    have h_x := this h, rw [h_x, a] at h_q, norm_num at h_q,
end,
have h_x := dec_em (x = -1), cases h_x, exact or.intro_right (x=1) h_x,
exfalso, 
have : 0 < 3*y^2, sorry,
sorry,


--have h_xx := or_iff_not_imp_left.1 h_x h,

--by_contradiction, rw not_or_distrib at a,
--cases a, 



sorry,
end


lemma coprime_dvd {a b c : ℤ} (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) : a ∣ b * c → a ∣ c := 
begin
intro, rw [← int.nat_abs_dvd, ← int.dvd_nat_abs, int.nat_abs_mul, int.coe_nat_dvd] at a_1,
have := coprime.dvd_of_dvd_mul_left h_ab a_1,
rw [← int.coe_nat_dvd, int.nat_abs_dvd, int.dvd_nat_abs] at this,
exact this,
end


lemma prime_coprime {a b p : ℤ} (hp : prime_int p) (h_ab : a>0 ∧ b>0) : p = a + b → coprime (int.nat_abs a) (int.nat_abs b) := 
begin
intro h,
have h1:= gcd_dvd (int.nat_abs a) (int.nat_abs b), 
rw [← int.coe_nat_dvd, int.dvd_nat_abs, ← int.coe_nat_dvd, int.dvd_nat_abs] at h1,
have h2:=dvd_add h1.1 h1.2, rw [h.symm, ← int.dvd_nat_abs, int.coe_nat_dvd] at h2,
unfold prime_int at hp, unfold prime at hp,
have h3:= hp.2 (gcd (int.nat_abs a) (int.nat_abs b)) h2, cases h3,
unfold coprime, exact h3,
have h4 := and.intro (int.le_of_dvd h_ab.1 h1.1) (int.le_of_dvd h_ab.2 h1.2),
have h5 : ↑(gcd (int.nat_abs a) (int.nat_abs b)) + ↑(gcd (int.nat_abs a) (int.nat_abs b)) ≤ a + b, sorry,
ring at h5, rw [h.symm, h3] at h5,
have h6 : p ≤ ↑(int.nat_abs p), sorry,
have h7 := le_trans h5 h6, exfalso,
have h8 : (↑(int.nat_abs p) : ℤ) ≠ (0 : ℤ), sorry,
have h9:= int.div_le_div (show ↑(int.nat_abs p) > (0:ℤ), from sorry) h7,--(int.coe_nat_ne_zero_iff_pos.1 h8) h7,
rw [(int.mul_div_cancel 2 h8), int.div_self h8] at h9,
exact h9,
end



lemma prime_int_ne_zero {p : ℤ} (hp : prime_int p) : p ≠ 0 := 
begin
unfold prime_int at hp,
have := prime.ne_zero hp,
norm_num, by_contradiction, rw a at this, simp at this, exact this,
end

lemma int_add_neg {a b c : ℤ} : a + (-b)*c = a - b*c := by norm_num

lemma g_zero_is_ne_zero {a : ℤ} : 0 < a → a ≠ 0 :=
by {intro, norm_num, by_contradiction, rw a_2 at a_1, norm_num at a_1}

lemma residue_rewrite {a b n : ℤ} : a % n = b ↔ ∃ k : ℤ, a = k * n + b := sorry

lemma odd_dvd_4 {a b : ℤ} (h : a % 2 = 1 ∧ b % 2 = 1) : 4 ∣ (b - a) ∨ 4 ∣ (b + a) := sorry

lemma n_even_if_coprime {a b : ℤ} : coprime (int.nat_abs a) (int.nat_abs b) → ¬(a % 2 = 0 ∧ b % 2 = 0) := sorry

lemma coprime_nat_abs_one {x y : ℤ} (h_x : x = 1 ∨ x = -1) (h_y : y = 1 ∨ y = -1) : coprime (int.nat_abs x) (int.nat_abs y) :=
begin 
cases h_x, cases h_y, 
rw [h_x, h_y], norm_num, exact gcd_self 1,
rw [h_x, h_y], norm_num, exact gcd_self 1,
cases h_y,
rw [h_x, h_y], norm_num, exact gcd_self 1,
rw [h_x, h_y], norm_num, exact gcd_self 1,
end


lemma gcd_dvd_mul_sum {a b c d q : ℤ} : (q = a * c + b * d) → ((gcd (int.nat_abs a) (int.nat_abs b) : ℤ)∣ q ):=
begin
have h1 := gcd_dvd (int.nat_abs a) (int.nat_abs b),
rw [←int.coe_nat_dvd, ←int.coe_nat_dvd] at h1,
have h2 := and.intro (int.dvd_nat_abs.1 h1.1) (int.dvd_nat_abs.1 h1.2),
have h3 := and.intro (dvd_mul_of_dvd_left h2.1 c) (dvd_mul_of_dvd_left h2.2 d),
intro, rw a_1, exact (dvd_add h3.1 h3.2),
end

lemma coprime_lemma {a b c d k l m n : ℤ} (ha : a = c*k + d*l) (hb : b = c * m + d * n) :
coprime (int.nat_abs a) (int.nat_abs b) → coprime (int.nat_abs c) (int.nat_abs d) :=
begin
intro, unfold coprime, by_contradiction, 
have h1 := gcd_dvd (int.nat_abs c) (int.nat_abs d),
rw [←int.coe_nat_dvd, ←int.coe_nat_dvd] at h1,
have h2 := and.intro (int.dvd_nat_abs.1 h1.1) (int.dvd_nat_abs.1 h1.2),
have ha_dvd := and.intro (dvd_mul_of_dvd_left h2.1 k) (dvd_mul_of_dvd_left h2.2 l),
have hb_dvd := and.intro (dvd_mul_of_dvd_left h2.1 m) (dvd_mul_of_dvd_left h2.2 n),
have h_dvd := and.intro (dvd_add ha_dvd.1 ha_dvd.2) (dvd_add hb_dvd.1 hb_dvd.2),
rw [ha.symm, hb.symm] at h_dvd,
rw [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd] at h_dvd,
have h_g_one: gcd (int.nat_abs c) (int.nat_abs d) > 1,
begin
    by_contradiction, simp at a_3, rw [(show 1 = 0 + 1, by refl), le_add_one_iff] at a_3,
    cases a_3, rw le_zero_iff at a_3,
    have h := and.intro (eq_zero_of_gcd_eq_zero_left a_3) (eq_zero_of_gcd_eq_zero_right a_3),
    have := and.intro (int.eq_zero_of_nat_abs_eq_zero h.1) (int.eq_zero_of_nat_abs_eq_zero h.2),
    rw [this.1, this.2] at ha, rw [this.1, this.2] at hb, simp at ha, simp at hb,
    have h5 : gcd (int.nat_abs a) (int.nat_abs b) = 0, {rw [ha, hb], simp},
    unfold coprime at a_1, rw h5 at a_1, simp at a_1, exact a_1,
    simp at a_3, exact absurd a_3 a_2,
end,
have := not_coprime_of_dvd_of_dvd h_g_one h_dvd.1 h_dvd.2,
exact absurd a_1 this,
end

lemma gcd_le {a b : ℕ} (h_a : a ≠ 0) (h_b : b ≠ 0) : gcd a b ≤ a ∧ gcd a b ≤ b := 
begin
have := gcd_dvd a b,
exact and.intro (le_of_dvd (pos_iff_ne_zero.2 h_a) this.1) (le_of_dvd (pos_iff_ne_zero.2 h_b) this.2),
end

lemma prime_coprime_mul {a b c d p : ℤ} (hp : prime_int p) : p = a * b + c * d → coprime (int.nat_abs a) (int.nat_abs c) ∨ gcd (int.nat_abs a) (int.nat_abs c) = int.nat_abs p:= 
begin
intro, unfold coprime, unfold prime_int at hp, unfold prime at hp,
have h1 := gcd_dvd_mul_sum a_1, rw [← int.dvd_nat_abs, int.coe_nat_dvd] at h1,
have := hp.2 (gcd (int.nat_abs a) (int.nat_abs c)) h1,
exact this,
end

lemma prime_int_dvd_mul {p m n : ℤ} (pp : prime_int p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := sorry



------------ lemmas for descent step ------------------


lemma lemma_1 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)):
(prime_int q ∨ q = 4 ∧ n = 3) → q ∣  n*(x*b - a*y)*(x*b + a*y) :=
begin
intro,
have h1 : q ∣ a^2 *(x^2 + n*y^2), {rw h_q, exact (dvd_mul_left _ _)},
have h2 := dvd_sub (dvd_mul_of_dvd_right h_q_dvd _) h1, 
have h3 : x ^ 2 * (a ^ 2 + n * b ^ 2) - a ^ 2 * (x ^ 2 + n * y ^ 2) = n*(x*b - a*y)*(x*b + a*y), by ring,
rw h3.symm, exact h2,
end

#check dvd_mul_of_dvd_left

lemma lemma_2 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) (a_1 : prime_int q ∨ q = 4 ∧ n = 3) (h1 :  q ∣ x * b - a * y): 
∃ (c d : ℤ), (a ^ 2 + n * b ^ 2) / q = c ^ 2 + n * d ^ 2 ∧ coprime (int.nat_abs c) (int.nat_abs d) :=
begin
cases h1 with d hd, rw [h_q, right_distrib, ← int_add_sub_r, int_add_sub_three_l] at hd,
rw (show x * b - x ^ 2 * d = x * (b - x * d), by ring) at hd, rw (show n * y ^ 2 * d + a * y = y * (n * y * d + a), by ring) at hd,
have h7 := dvd.intro_left _ (show (b - x * d) * x = y * (n * y * d + a), {rw hd.symm, ring}),
have h8_ : q = x * x + y * (n * y), 
{ring, rw (show y ^ 2 * n + x ^ 2 = x^2 + n * y^2, by ring), exact h_q,},
have h8_ : coprime (int.nat_abs x) (int.nat_abs y),
begin
    cases a_1, cases prime_coprime_mul a_1 h8_, exact h,
    exfalso, 
    have h1 := gcd_dvd (int.nat_abs x) (int.nat_abs y),
    rw [←int.coe_nat_dvd, ←int.coe_nat_dvd] at h1,
    have h2 := and.intro (int.dvd_nat_abs.1 h1.1) (int.dvd_nat_abs.1 h1.2),
    -- have h3 := and.intro (dvd_mul_of_dvd_left h2.1 x) (dvd_mul_of_dvd_left h2.2 (n*y)),
    -- have h4 : ↑(gcd (int.nat_abs x) (int.nat_abs y)) ∣ q , 
    -- {rw h_q, rw (show x^2 + n*y^2 = x*x + y*(n*y), by ring), exact dvd_add h3.1 h3.2},
    -- unfold prime_int at a_1, unfold prime at a_1, rw ← nat_abs_dvd at h4,
    -- have h5 := a_1.2 (gcd (int.nat_abs x) (int.nat_abs y)) h4,
    sorry,
    have h_x : x = 1 ∨ x = -1, sorry,
    have h_y : y = 1 ∨ y = -1, sorry,
    exact coprime_nat_abs_one h_x h_y,
end,
have h9 := coprime_dvd h8_ h7, cases h9 with c hc,
have h_x : x ≠ 0, sorry,
rw [hc, (show y*(x*c) = x * (c*y), by ring), domain.mul_left_inj h_x,
← int_add_sub_r, (show x * d = d * x, by ring)] at hd,
have h10 := identity c d n x y, rw [h_q.symm, hd.symm] at h10,
have h11 : c * x - n * d * y = a, {rw (int_add_sub_l'.1 hc), ring}, rw h11 at h10,
have h12 : q ≠ 0, {cases a_1, exact prime_int_ne_zero a_1, rw a_1.1, norm_num},
have := (int.div_eq_iff_eq_mul_left h12 h_q_dvd).2 h10.symm,
existsi c, existsi d, split, exact this,
have h_a : a = c * x + d * (-n * y), {rw h11.symm, ring},
exact coprime_lemma h_a hd h_ab,
end

lemma lemma_3 {q n x y a b : ℤ} (h_x : x = 1 ∨ x = -1) (h_y : y = 1 ∨ y = -1) :
4 ∣ (x * b - a * y) * (x * b + a * y) → 4 ∣ (b - a) * (b + a) := 
begin 
intro,
cases h_x, cases h_y,
rw [h_x, h_y] at a_1, simp at a_1,
rw (show (b - a) * (b + a) = (b + -a) * (a + b), by ring), exact a_1,
rw [h_x, h_y] at a_1, simp at a_1,
rw (show (b - a) * (b + a) = (a + b) * (b + -a), by ring), exact a_1,
cases h_y,
rw [h_x, h_y] at a_1, simp at a_1,
rw (show (b - a) * (b + a) = (-a + -b) * (a + -b), by ring), exact a_1,
rw [h_x, h_y] at a_1, simp at a_1,
rw (show (b - a) * (b + a) = (a + -b) * (-a + -b), by ring), exact a_1,
end



lemma lemma_1_q_prime {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) : 
prime_int q → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (coprime (int.nat_abs c) (int.nat_abs d))) := 
begin
intro,
have h1 := (prime_int_dvd_mul a_1).1 (lemma_1 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1)),
cases h1, rw (prime_int_dvd_mul a_1) at h1, cases h1,
have h2 : q = n, sorry,
rw h2 at h_q_dvd, rw h2 at a_1, rw h2 at h_q,
have h3 : n ∣ a^2, from (dvd_add_iff_left (show n ∣ n*(b^2), from dvd_mul_right n (b^2))).2 h_q_dvd,
rw [(show a^2 = a* a, by ring), (prime_int_dvd_mul a_1)] at h3, simp at h3,
rcases (exists_eq_mul_right_of_dvd h3) with d,
let c := b,
rcases (exists_eq_mul_right_of_dvd h_q_dvd) with m,
have h4 : n ≠ 0, from g_zero_is_ne_zero h_n,
rw ← (int.div_eq_iff_eq_mul_right h4 h_q_dvd) at h_1,
have b_1 := h_1,
rw [(int.add_mul_div_left _ _ h4), (show a^2 = a* a, by ring), h, (show b = c, by refl), (show n * d * (n * d) = (n * d) * n * d, from sorry)] at h_1,
simp at h_1,
have h_11 : c ^ 2 + n * d * n * d / n = c ^ 2 + n * d * (n * d / n), 
{simp, rw (show n * d * n * d / n = n * d * (n * d / n), from sorry)}, 
rw [h_11, (@int.mul_div_cancel_left n d h4), (show n*d*d = n*(d*d), by ring), (show d*d = d^2, by ring)] at h_1,
rw [h2.symm, h_1.symm, (show (a ^ 2 + q * b ^ 2) = (a ^ 2 + n * b ^ 2), by {rw h2})] at b_1,
existsi c, existsi d, split, exact b_1, 
--
unfold coprime, unfold coprime at h_ab, rw [(show c = b, by refl), (show d = a/n, from (int.div_eq_of_eq_mul_right h4 h).symm)],
have h6 : gcd (int.nat_abs b) (int.nat_abs (a / n)) = gcd (int.nat_abs a) (int.nat_abs b), sorry,
rw h6, exact h_ab,
-----
exact (lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1),
-----
let y_ := -y, rw [(show y = -y_, by norm_num) , (show (-y_)^2 = y_^2, by norm_num)] at h_q,
rw [(show a*y = -a * y_, by norm_num), int_add_neg] at h1,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1,
end


lemma lemma_1_q_4_n_3 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_xy : coprime (int.nat_abs x) (int.nat_abs y))
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) : 
(q = (4:ℤ) ∧ n = (3:ℤ)) → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (coprime (int.nat_abs c) (int.nat_abs d))) := 
begin
intro, 
have h1 : a % 2 = 1 ∧ b % 2 = 1,
begin 
    rw [a_1.1, a_1.2] at h_q_dvd,
    cases int.mod_two_eq_zero_or_one a,
    rw h, sorry,
    split, exact h,
    by_contradiction,
    have h_b : b % 2 = 0, from or_iff_not_imp_right.1 (int.mod_two_eq_zero_or_one b) a_2,
    rcases (residue_rewrite.1 h) with m, rcases (residue_rewrite.1 h_b) with l, simp at h_2,
    rw [h_1, h_2] at h_q_dvd,
    ring at h_q_dvd,
    rw  (show (4 * m + 4) * m = 4 * (m * m + m), by ring) at h_q_dvd,
    have h1: 4 ∣ 4 * (m * m + m), by simp,
    rw ← (dvd_add_iff_right h1) at h_q_dvd,
    rw (show 12 * l ^ 2 = 4 * (3 * l ^2), by ring) at h_q_dvd,
    have h2 : 4 ∣ 4 * (3 * l ^ 2), by simp,
    rw ← (dvd_add_iff_right h2) at h_q_dvd,
    have : ¬ (4:ℤ) ∣ (1: ℤ), by norm_num,
    exact absurd h_q_dvd this,
end,
have h_x : x = 1 ∨ x = -1, sorry,
have h_y : y = 1 ∨ y = -1, sorry,
have h2 := odd_dvd_4 h1,
cases h2, cases h_x, cases h_y,
have h3 : q ∣ x*b - a*y, {rw h_x, rw h_y, simp, rw a_1.1, exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
let y_ := -y, rw [(show y = -y_, by norm_num) , (show (-y_)^2 = y_^2, by norm_num)] at h_q,
have h_y_ : y_ = 1, {rw [(show y_ = -y, by norm_num), h_y], simp},
have h3 : q ∣ x*b - a*y_, {rw h_x, rw h_y_, simp, rw a_1.1, exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
cases h_y,
let x_ := -x, rw [(show x = -x_, by norm_num) , (show (-x_)^2 = x_^2, by norm_num)] at h_q,
have h_x_ : x_ = 1, {rw [(show x_ = -x, by norm_num), h_x], simp},
have h3 : q ∣ x_*b - a*y, {rw h_y, rw h_x_, simp, rw a_1.1, exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
let x_ := -x, rw [(show x = -x_, by norm_num) , (show (-x_)^2 = x_^2, by norm_num)] at h_q,
have h_x_ : x_ = 1, {rw [(show x_ = -x, by norm_num), h_x], simp},
let y_ := -y, rw [(show y = -y_, by norm_num) , (show (-y_)^2 = y_^2, by norm_num)] at h_q,
have h_y_ : y_ = 1, {rw [(show y_ = -y, by norm_num), h_y], simp},
have h3 : q ∣ x_*b - a*y_, {rw h_y_, rw h_x_, simp, rw a_1.1, exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
cases h_x, cases h_y,
let y_ := -y, rw [(show y = -y_, by norm_num) , (show (-y_)^2 = y_^2, by norm_num)] at h_q,
have h_y_ : y_ = -1, {rw [(show y_ = -y, by norm_num), h_y]},
have h3 : q ∣ x*b - a*y_, {rw h_y_, rw h_x, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
have h3 : q ∣ x*b - a*y, {rw h_y, rw h_x, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
cases h_y,
let x_ := -x, rw [(show x = -x_, by norm_num) , (show (-x_)^2 = x_^2, by norm_num)] at h_q,
have h_x_ : x_ = 1, {rw [(show x_ = -x, by norm_num), h_x], simp},
let y_ := -y, rw [(show y = -y_, by norm_num) , (show (-y_)^2 = y_^2, by norm_num)] at h_q,
have h_y_ : y_ = -1, {rw [(show y_ = -y, by norm_num), h_y]},
have h3 : q ∣ x_*b - a*y_, {rw h_y_, rw h_x_, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
let x_ := -x, rw [(show x = -x_, by norm_num) , (show (-x_)^2 = x_^2, by norm_num)] at h_q,
have h_x_ : x_ = 1, {rw [(show x_ = -x, by norm_num), h_x], simp},
have h3 : q ∣ x_*b - a*y, {rw h_y, rw h_x_, simp, rw a_1.1, rw (show a + b = b + a, by norm_num), exact h2},
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_right (prime_int q) a_1) h3,
end

------------ lemmas for reciprocity step ------------------



lemma lemma_4 {n p: ℤ} (h_n : n ≠ 0) (hp : prime_int p ∧ int.nat_abs p ≠ 2) (h_dvd : ¬ p ∣ n ) : 
(∃  x y : ℤ, p ∣ x^2 + n*y^2 ∧ coprime (int.nat_abs x) (int.nat_abs y)) ↔ legendre_sym (-n) hp = 1 := 
begin
split, unfold legendre_sym, intro, cases a with x hx, cases hx with y h,
sorry,
intro, 
have h1 : ∃ x : ℤ, -n ≡ x^2 [ZMOD ↑(int.nat_abs p)], sorry,
cases h1 with x hx,
have h2 : ↑(int.nat_abs p) = p, sorry,
rw [h2, int.modeq.modeq_iff_dvd, (show x^2 - -n = x^2 + n*1^2, by ring)] at hx, 
existsi x, existsi (1:ℤ),
rw (show int.nat_abs 1 = 1, by norm_num),
exact and.intro hx (coprime_one_right (int.nat_abs x)),
end



lemma descent_step_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ a b : ℤ, p ∣ (a^2 + b^2) ∧ (coprime (int.nat_abs a) (int.nat_abs b))) → (∃ x y : ℤ, p = x^2 + y^2) := 
begin
intro ha, rcases ha with a, rcases ha_h with b, 




sorry,
end

lemma descent_step_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b))) → ∃ x y : ℤ, p = x^2 + 2*y^2 := sorry

lemma descent_step_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b))) → ∃ x y : ℤ, p = x^2 + 3*y^2 := sorry


lemma reciprocity_step_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
p ≡ 1 [ZMOD 4] → ∃ a b : ℤ, (p ∣ (a^2 + b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry

lemma reciprocity_step_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) → ∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry

lemma reciprocity_step_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
((p = 3) ∨ (p ≡ 1 [ZMOD 3])) → ∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry


theorem Thm_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ x y : ℤ, p = x^2 + y^2) ↔ p ≡ 1 [ZMOD 4] := 
begin
split, intro, cases a with x, cases a_h with y h,
have h1 := odd_prime_int_is_odd hp,
have h_xy : (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0), 
begin
    have h_x := int.mod_two_eq_zero_or_one x, cases h_x, 
    have h_y := int.mod_two_eq_zero_or_one y, cases h_y, 
    rcases (exists_eq_mul_right_of_dvd ((int.dvd_iff_mod_eq_zero 2 x).2 h_x)) with m,
    rw h_1 at h,
    rcases (exists_eq_mul_right_of_dvd ((int.dvd_iff_mod_eq_zero 2 y).2 h_y)) with n,
    rw h_2 at h,
    rw (show (2 * m) ^ 2 + (2 * n) ^ 2 = 2 * (2*m^2+2*n^2), by ring) at h, 
    have := dvd_mul_right 2 (2 * m ^ 2 + 2 * n ^ 2), rw h.symm at this,
    rw int.dvd_iff_mod_eq_zero at this, rw h1 at this, exfalso, simp at this, exact this,
    exact or.intro_left (x % 2 = 1 ∧ y % 2 = 0) (and.intro h_x h_y),
    have h_y := int.mod_two_eq_zero_or_one y, cases h_y, 
    exact or.intro_right (x % 2 = 0 ∧ y % 2 = 1) (and.intro h_x h_y),
    have h2 := int.modeq.mod_modeq x 2, rw h_x at h2,
    have h3 := int.modeq.mod_modeq y 2, rw h_y at h3,
    have h_5 : ↑(int.nat_abs 2) = (2:ℤ), by ring,rw h_5 at h2, rw h_5 at h3,
    rw int.modeq.modeq_iff_dvd at h2, rw int.modeq.modeq_iff_dvd at h3,
    rcases h2 with k, rcases h3 with l,
    rw ← int_add_sub_r at h2_h, rw ← int_add_sub_r at h3_h,
    rw [h2_h, h3_h, (show (2 * k + 1) ^ 2 + (2 * l + 1) ^ 2 = 2 * (2*k^2 + 2*k + 2*l^2 + 2*l + 1), by ring)] at h,
    have := dvd_mul_right 2 (2 * k ^ 2 + 2 * k + 2 * l ^ 2 + 2 * l + 1), rw h.symm at this,
    rw [int.dvd_iff_mod_eq_zero, h1] at this, 
    exfalso, simp at this, exact this,
end,
cases h_xy,
have h_x := int.modeq.mod_modeq x 2,rw h_xy.1 at h_x,
have h_y := int.modeq.mod_modeq y 2,rw h_xy.2 at h_y,
have h_2 : ↑(int.nat_abs 2) = (2:ℤ), by ring, rw h_2 at h_x, rw h_2 at h_y,
rw int.modeq.modeq_iff_dvd at h_x, rw int.modeq.modeq_iff_dvd at h_y,
cases h_x with k h_x, cases h_y with l h_y, rw ← int_add_sub_r at h_y, simp at h_x,
rw [h_x, h_y,(show (2 * k) ^ 2 + (2 * l + 1) ^ 2 = 4 * (k^2 + l^2 +l) +1, by ring)] at h,
rw int_add_sub_r at h,
have := dvd_mul_right 4 (k ^ 2 + l ^ 2 + l), rw h.symm at this,
rw ← int.modeq.modeq_zero_iff at this, 
have h2 := int.modeq.modeq_add this (show 1 ≡ 1 [ZMOD 4], by refl),
simp at h2, exact h2,
---------
have h_x := int.modeq.mod_modeq x 2,rw h_xy.1 at h_x,
have h_y := int.modeq.mod_modeq y 2,rw h_xy.2 at h_y,
have h_2 : ↑(int.nat_abs 2) = (2:ℤ), by ring, rw h_2 at h_x, rw h_2 at h_y,
rw int.modeq.modeq_iff_dvd at h_x, rw int.modeq.modeq_iff_dvd at h_y,
cases h_x with k h_x, cases h_y with l h_y, rw ← int_add_sub_r at h_x, simp at h_y,
rw [h_x, h_y,(show (2 * k + 1) ^ 2 + (2 * l) ^ 2 = 4 * (k^2 + l^2 +k) +1, by ring)] at h,
rw int_add_sub_r at h,
have := dvd_mul_right 4 (k ^ 2 + l ^ 2 + k), rw h.symm at this,
rw ← int.modeq.modeq_zero_iff at this, 
have h2 := int.modeq.modeq_add this (show 1 ≡ 1 [ZMOD 4], by refl),
simp at h2, exact h2,
---------
intro ha, exact descent_step_1 hp (reciprocity_step_1 hp ha),
end

theorem Thm_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ x y : ℤ, p = x^2 + 2*y^2) ↔ ((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) := 
begin split,
sorry,
intro ha, exact descent_step_2 hp (reciprocity_step_2 hp ha),
end

theorem Thm_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
(∃ x y : ℤ, p = x^2 + 3*y^2) ↔ ((p = 3) ∨ (p ≡ 1 [ZMOD 3])) :=
begin split, intro ha, cases (dec_em (p = 3)),
exact or.intro_left (p ≡ 1 [ZMOD 3]) h, 
rcases ha with x , rcases ha_h with y,
have h_x_ne_3 : x ≠ 3, 
begin
    by_contradiction, simp at a, 
    rw [a, (show 3 ^ 2 + 3 * y ^ 2 = 3 * (3+y^2), by ring)] at ha_h_h,
    have := dvd_mul_right 3 (3+y^2), rw ha_h_h.symm at this,
    unfold prime_int at hp, unfold prime at hp,
    have h1 := hp.1.2 3 (int.dvd_nat_abs_of_of_nat_dvd this),
    have h2 : ¬ 3 = int.nat_abs p, sorry,
    norm_num at h1, exact absurd h1 h2,
end,

sorry,
intro ha, exact descent_step_3 hp (reciprocity_step_3 hp ha),
end

