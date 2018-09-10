import algebra.ordered_ring
import M3P14.lqr


open int

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


lemma lemma_xy {q n x y : ℤ} (h_q : q = x^2 + n*y^2) (hq : q = 4 ∧ n = 3) (h_xy : nat.coprime (nat_abs x) (nat_abs y)): 
(x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) := 
begin
split, cases (dec_em (x = 1)), exact or.intro_left (x = -1) h,
rw [hq.1, hq.2] at h_q,
have : y ≠ 0,
begin
    by_contradiction, unfold nat.coprime at h_xy, simp at a, rw a at h_xy, simp at h_xy, 
    have := nat_abs_eq x, rw h_xy at this, simp at this,
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


lemma nat.coprime_dvd {a b c : ℤ} (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : a ∣ b * c → a ∣ c := 
begin
intro, rw [← nat_abs_dvd, ← dvd_nat_abs, nat_abs_mul, coe_nat_dvd] at a_1,
have := nat.coprime.dvd_of_dvd_mul_left h_ab a_1,
rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs] at this,
exact this,
end


lemma prime_nat.coprime {a b p : ℤ} (hp : prime_int p) (h_ab : a>0 ∧ b>0) :
p = a + b → nat.coprime (nat_abs a) (nat_abs b) := 
begin
intro h,
have h1:= nat.gcd_dvd (nat_abs a) (nat_abs b), 
rw [← coe_nat_dvd, dvd_nat_abs, ← coe_nat_dvd, dvd_nat_abs] at h1,
have h2:=dvd_add h1.1 h1.2, rw [h.symm, ← dvd_nat_abs, coe_nat_dvd] at h2,
unfold prime_int at hp, unfold nat.prime at hp,
have h3:= hp.2 (gcd (nat_abs a) (nat_abs b)) h2, cases h3,
unfold nat.coprime, exact h3,
have h4 := and.intro (le_of_dvd h_ab.1 h1.1) (le_of_dvd h_ab.2 h1.2),
have h5 : ↑(gcd (nat_abs a) (nat_abs b)) + ↑(gcd (nat_abs a) (nat_abs b)) ≤ a + b, sorry,
ring at h5, rw [h.symm, h3] at h5,
have h6 : p ≤ ↑(nat_abs p), begin
  cases (nat_abs_eq p), finish, rw h_1, simp, sorry,


end,
have h7 := le_trans h5 h6, exfalso,
have h8 : (↑(nat_abs p) : ℤ) ≠ (0 : ℤ), sorry,
have h9:= int.div_le_div (show ↑(nat_abs p) > (0:ℤ), from sorry) h7,--(coe_nat_ne_zero_iff_pos.1 h8) h7,
rw [(int.mul_div_cancel 2 h8), int.div_self h8] at h9,
exact h9,
end



lemma prime_int_ne_zero {p : ℤ} (hp : prime_int p) : p ≠ 0 := 
begin
unfold prime_int at hp,
have := nat.prime.ne_zero hp,
norm_num, by_contradiction, rw a at this, simp at this, exact this,
end

lemma int_add_neg {a b c : ℤ} : a + (-b)*c = a - b*c := by norm_num

lemma g_zero_is_ne_zero {a : ℤ} : 0 < a → a ≠ 0 :=
by {intro, norm_num, by_contradiction, rw a_2 at a_1, norm_num at a_1}

lemma residue_rewrite {a b n : ℤ} : a % n = b ↔ ∃ k : ℤ, a = k * n + b := sorry

lemma odd_dvd_4 {a b : ℤ} (h : a % 2 = 1 ∧ b % 2 = 1) : 4 ∣ (b - a) ∨ 4 ∣ (b + a) := sorry

lemma not_even_if_coprime {a b : ℤ} : nat.coprime (nat_abs a) (nat_abs b) → ¬(a % 2 = 0 ∧ b % 2 = 0) := sorry

lemma coprime_nat_abs_one {x y : ℤ} (h_x : x = 1 ∨ x = -1) (h_y : y = 1 ∨ y = -1) : nat.coprime (nat_abs x) (nat_abs y) :=
begin 
cases h_x, cases h_y, 
rw [h_x, h_y], norm_num, exact nat.gcd_self 1,
rw [h_x, h_y], norm_num, exact nat.gcd_self 1,
cases h_y,
rw [h_x, h_y], norm_num, exact nat.gcd_self 1,
rw [h_x, h_y], norm_num, exact nat.gcd_self 1,
end


lemma gcd_dvd_mul_sum {a b c d q : ℤ} : (q = a * c + b * d) → ((gcd (nat_abs a) (nat_abs b) : ℤ)∣ q ):=
begin
have h1 := nat.gcd_dvd (nat_abs a) (nat_abs b),
rw [←coe_nat_dvd, ←coe_nat_dvd] at h1,
have h2 := and.intro (dvd_nat_abs.1 h1.1) (dvd_nat_abs.1 h1.2),
have h3 := and.intro (dvd_mul_of_dvd_left h2.1 c) (dvd_mul_of_dvd_left h2.2 d),
intro, rw a_1, exact (dvd_add h3.1 h3.2),
end

lemma coprime_lemma {a b c d k l m n : ℤ} (ha : a = c*k + d*l) (hb : b = c * m + d * n) :
nat.coprime (nat_abs a) (nat_abs b) → nat.coprime (nat_abs c) (nat_abs d) :=
begin
intro, unfold nat.coprime, by_contradiction, 
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
    by_contradiction, simp at a_3, rw [(show (1:ℕ) = 0 + 1, by refl), nat.le_add_one_iff] at a_3,
    cases a_3, rw nat.le_zero_iff at a_3,
    have h := and.intro (nat.eq_zero_of_gcd_eq_zero_left a_3) (nat.eq_zero_of_gcd_eq_zero_right a_3),
    have := and.intro (eq_zero_of_nat_abs_eq_zero h.1) (eq_zero_of_nat_abs_eq_zero h.2),
    rw [this.1, this.2] at ha, rw [this.1, this.2] at hb, simp at ha, simp at hb,
    have h5 : nat.gcd (nat_abs a) (nat_abs b) = 0, {rw [ha, hb], simp},
    unfold nat.coprime at a_1, rw h5 at a_1, simp at a_1, exact a_1,
    simp at a_3, exact absurd a_3 a_2,
end,
have := nat.not_coprime_of_dvd_of_dvd h_g_one h_dvd.1 h_dvd.2,
exact absurd a_1 this,
end

lemma gcd_le {a b : ℕ} (h_a : a ≠ 0) (h_b : b ≠ 0) : gcd a b ≤ a ∧ gcd a b ≤ b := 
begin
have := nat.gcd_dvd a b,
exact and.intro (nat.le_of_dvd (nat.pos_iff_ne_zero.2 h_a) this.1) (nat.le_of_dvd (nat.pos_iff_ne_zero.2 h_b) this.2),
end

lemma prime_coprime_mul {a b c d p : ℤ} (hp : prime_int p) : p = a * b + c * d → nat.coprime (nat_abs a) (nat_abs c) ∨ nat.gcd (nat_abs a) (nat_abs c) = nat_abs p:= 
begin
intro, unfold nat.coprime, unfold prime_int at hp, unfold nat.prime at hp,
have h1 := gcd_dvd_mul_sum a_1, rw [← dvd_nat_abs, coe_nat_dvd] at h1,
have := hp.2 (gcd (nat_abs a) (nat_abs c)) h1,
exact this,
end

lemma prime_int_dvd_mul {p m n : ℤ} (pp : prime_int p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := sorry

lemma zero_le_square (a : ℤ) : a^2 ≥ 0 := sorry


------------ lemmas for descent step ------------------


lemma lemma_1 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)):
(prime_int q ∨ q = 4 ∧ n = 3) → q ∣  n*(x*b - a*y)*(x*b + a*y) :=
begin
intro,
have h1 : q ∣ a^2 *(x^2 + n*y^2), {rw h_q, exact (dvd_mul_left _ _)},
have h2 := dvd_sub (dvd_mul_of_dvd_right h_q_dvd _) h1, 
have h3 : x ^ 2 * (a ^ 2 + n * b ^ 2) - a ^ 2 * (x ^ 2 + n * y ^ 2) = n*(x*b - a*y)*(x*b + a*y), by ring,
rw h3.symm, exact h2,
end

lemma lemma_1_q_4_n_3_x_y {q n x y a b : ℤ} (h_q : q = x^2 + n*y^2) (h_xy : nat.coprime (nat_abs x) (nat_abs y)) : 
(q = (4:ℤ) ∧ n = (3:ℤ)) →  (x = (1:ℤ) ∨ x = (-1:ℤ)) ∧ (y = (1:ℤ) ∨ y = (-1:ℤ)) := sorry

lemma lemma_2 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) (a_1 : prime_int q ∨ q = 4 ∧ n = 3) (h1 :  q ∣ x * b - a * y): 
∃ (c d : ℤ), (a ^ 2 + n * b ^ 2) / q = c ^ 2 + n * d ^ 2 ∧ nat.coprime (nat_abs c) (nat_abs d) :=
begin
cases h1 with d hd,
rw [h_q, right_distrib, ← int_add_sub_r, int_add_sub_three_l,
(show x * b - x ^ 2 * d = x * (b - x * d), by ring),
(show n * y ^ 2 * d + a * y = y * (n * y * d + a), by ring)] at hd,
have h7 := dvd.intro_left _ (show (b - x * d) * x = y * (n * y * d + a), {rw hd.symm, ring}),
have h8_ : q = x * x + y * (n * y), 
{ring, rw (show y ^ 2 * n + x ^ 2 = x^2 + n * y^2, by ring), exact h_q,},
have h8_ : nat.coprime (nat_abs x) (nat_abs y),
begin
  cases a_1, cases prime_coprime_mul a_1 h8_, exact h,
  
  exfalso,
  have zero_le_q: 0 ≤ q, sorry,
  have zero_lt_q : 0 < q,
  {rw le_iff_eq_or_lt at zero_le_q, cases zero_le_q, exfalso, unfold prime_int at a_1,
  rw zero_le_q.symm at a_1, exact absurd a_1 nat.not_prime_zero, exact zero_le_q},
  have h1:= of_nat_nat_abs_eq_of_nonneg zero_le_q,
  have h2: ↑(nat_abs q) = of_nat (nat_abs q), by refl,
  rw [←int.coe_nat_eq_coe_nat_iff, eq.trans h2 h1] at h,
  have h3 := nat.gcd_dvd (nat_abs x) (nat_abs y),
  rw [←coe_nat_dvd, ←coe_nat_dvd, h] at h3,
  -- replace h3 := and.intro (dvd_mul_of_dvd_left h3.1 ↑(nat_abs x)) (dvd_mul_of_dvd_left h3.2 ↑(nat_abs y)),
  -- have h_x_1 : ↑(nat_abs x) * ↑(nat_abs x) = ↑((nat_abs x)*(nat_abs x)), by sorry,
  -- have h_y_1 : ↑(nat_abs y) * ↑(nat_abs y) = ↑((nat_abs y)*(nat_abs y)), by sorry,
  -- rw h_x_1 at h3, rw h_y_1 at h3, 
  replace h3 : (q ∣ x^2) ∧ (q ∣ n*y^2), from sorry,
  replace h3 := and.intro (le_of_dvd (show x^2>0, from sorry) h3.1) (le_of_dvd (show n*y^2>0, from sorry) h3.2),
  have := add_le_add' h3.1 h3.2,
  rw [h_q.symm, (one_mul q).symm, (show 1 * q + 1 * q = 2 * q, by ring),
  mul_le_mul_right zero_lt_q] at this, 
  exact this,

  have := lemma_1_q_4_n_3_x_y,










    -- have := prime_coprime_mul a_1 h8_,
    -- cases prime_coprime_mul a_1 h8_, exact h,
    -- exfalso, 
    -- have h1 := nat.gcd_dvd (nat_abs x) (nat_abs y),
    -- rw [←coe_nat_dvd, ←coe_nat_dvd] at h1,
    -- have h2 := and.intro (dvd_nat_abs.1 h1.1) (dvd_nat_abs.1 h1.2),


    -- have h3 := and.intro (dvd_mul_of_dvd_left h2.1 x) (dvd_mul_of_dvd_left h2.2 (n*y)),
    -- have h4 : ↑(gcd (nat_abs x) (nat_abs y)) ∣ q , 
    -- {rw h_q, rw (show x^2 + n*y^2 = x*x + y*(n*y), by ring), exact dvd_add h3.1 h3.2},
    -- unfold prime_int at a_1, unfold prime at a_1, rw ← nat_abs_dvd at h4,
    -- have h5 := a_1.2 (gcd (nat_abs x) (nat_abs y)) h4,
    sorry,
    have h_x : x = 1 ∨ x = -1, sorry,
    have h_y : y = 1 ∨ y = -1, sorry,
    exact coprime_nat_abs_one h_x h_y,
end,
have h9 := nat.coprime_dvd h8_ h7, cases h9 with c hc,
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

lemma lemma_1_a_b_odd {a b n q : ℤ} (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) :
(q = (4:ℤ) ∧ n = (3:ℤ)) → (a % 2 = 1 ∧ b % 2 = 1) := begin
intro h,
rw [h.1, h.2] at h_q_dvd,

rcases (mod_two_eq_zero_or_one a) with ha, exfalso,
have hb := or_iff_not_imp_left.1 (mod_two_eq_zero_or_one b) (not_and.1 (not_even_if_coprime h_ab) ha),
cases (dvd_of_mod_eq_zero ha) with k hk,
replace hb := eq.trans hb (show (1:ℤ) = (1:ℤ) % (2:ℤ), by refl),
cases (dvd_of_mod_eq_zero (mod_eq_mod_iff_mod_sub_eq_zero.1 hb)) with l hl,
rw ← int_add_sub_r at hl,
rw [hl, hk, (show (2 * k) ^ 2 + (3:ℤ) * (2 * l + 1) ^ 2 = 4 * (k^2 + 3*l^2 + 3*l) + (3:ℤ), by ring)] at h_q_dvd, 
replace h_q_dvd := (dvd_add_iff_right (dvd_mul_right (4:ℤ) (k ^ 2 + 3 * l ^ 2 + 3 * l))).2 h_q_dvd,
norm_num at h_q_dvd,

replace h_1 := eq.trans h_1 (show (1:ℤ) = (1:ℤ) % (2:ℤ), by refl),
cases (dvd_of_mod_eq_zero (mod_eq_mod_iff_mod_sub_eq_zero.1 h_1)) with k hk,
rw ← int_add_sub_r at hk, rw hk at h_q_dvd,

cases (mod_two_eq_zero_or_one b) with hb, exfalso,
cases (dvd_of_mod_eq_zero hb) with l hl,
rw [hl, (show (2 * k + 1) ^ 2 + 3 * (2 * l) ^ 2 = 4 * (k^2 + k + 3*l^2) + 1, by ring)] at h_q_dvd,
replace h_q_dvd := (dvd_add_iff_right (dvd_mul_right 4 (k ^ 2 + k + 3 * l ^ 2))).2 h_q_dvd,
norm_num at h_q_dvd,
exact and.intro h_1 h_2,
end


lemma lemma_1_q_prime {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
prime_int q → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (nat.coprime (nat_abs c) (nat_abs d))) := 
begin
intro,
have h1 := (prime_int_dvd_mul a_1).1 (lemma_1 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1)),
cases h1, rw (prime_int_dvd_mul a_1) at h1,
----
cases h1,
have h2 : q = n, sorry,
rw h2 at h_q_dvd, rw h2 at a_1, rw h2 at h_q,
have h3 := (dvd_add_iff_left (dvd_mul_right n (b^2))).2 h_q_dvd,
rw [((show a^2 = a*a, by ring)), (prime_int_dvd_mul a_1)] at h3, simp at h3,
rcases (exists_eq_mul_right_of_dvd h3) with d,
let c := b,
rcases (exists_eq_mul_right_of_dvd h_q_dvd) with m,
have h4 := g_zero_is_ne_zero h_n,
rw ← (int.div_eq_iff_eq_mul_right h4 h_q_dvd) at h_1,
have b_1 := h_1,
rw [(int.add_mul_div_left _ _ h4), (show a^2 = a* a, by ring), h, (show b = c, by refl), (show n * d * (n * d) = (n * d) * n * d, from sorry)] at h_1,
simp at h_1,
have h_11 : c ^ 2 + n * d * n * d / n = c ^ 2 + n * d * (n * d / n), 
{simp, rw (show n * d * n * d / n = n * d * (n * d / n), by sorry)}, 
rw [h_11, (@int.mul_div_cancel_left n d h4), (show n*d*d = n*(d*d), by ring), (show d*d = d^2, by ring)] at h_1,
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
exact (lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1),
-----
let y_ := -y, rw (show y^2 = y_^2, by norm_num) at h_q,
rw [(show a*y = -a * y_, by norm_num), int_add_neg] at h1,
exact lemma_2 h_n h_q h_q_dvd h_ab (or.intro_left (q = 4 ∧ n = 3) a_1) h1,
end


lemma lemma_1_q_4_n_3 {q n x y a b : ℤ} (h_n : (0: ℤ) < n) (h_q : q = x^2 + n*y^2) (h_xy : nat.coprime (nat_abs x) (nat_abs y))
(h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : nat.coprime (nat_abs a) (nat_abs b)) : 
(q = (4:ℤ) ∧ n = (3:ℤ)) → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (nat.coprime (nat_abs c) (nat_abs d))) := 
begin
intro, 
have h1 := lemma_1_a_b_odd h_q_dvd h_ab a_1,
have h_x_y := lemma_1_q_4_n_3_x_y h_q h_xy a_1,
have h_x := h_x_y.1, have h_y := h_x_y.2,
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
exact x, exact y,
end

------------ lemmas for reciprocity step ------------------



lemma lemma_4 {n p: ℤ} (h_n : n ≠ 0) (hp : prime_int p ∧ nat_abs p ≠ 2) (h_dvd : ¬ p ∣ n ) (zero_le_p : 0 ≤ p): 
(∃  x y : ℤ, p ∣ x^2 + n*y^2 ∧ nat.coprime (nat_abs x) (nat_abs y)) ↔ legendre_sym (-n) hp = 1 := 
begin
split, intro, cases a with x hx, cases hx with y h,
--have hpp : p = ↑(nat_abs p), sorry,
have h1: x*x ≡ -n*y*y [ZMOD ↑(nat_abs p)], sorry,
--rw hpp at h1,
have h2: pos_nat (nat_abs p), sorry,
rw ←(@@zmod.eq_iff_modeq_int h2) at h1,
sorry,
intro h, unfold legendre_sym at h, split_ifs at h,
unfold quadratic_res at h_1,
cases h_1.1 with x hx,
have h2 : ↑(nat_abs p) = p, 
{
  cases (nat_abs_eq p), exact h_2.symm,
  exfalso, rw [h_2, ←(mul_le_mul_right_of_neg (show (-1:ℤ) < 0, by norm_num))] at zero_le_p, 
  simp at zero_le_p,
  rw [(show (0:ℤ) = ↑(0:ℕ), by refl), coe_nat_le, nat.le_zero_iff] at zero_le_p,
  exact absurd zero_le_p (nat.prime.ne_zero hp.1),
},
rw [h2, modeq.modeq_iff_dvd, (show x^2 - -n = x^2 + n*1^2, by ring)] at hx, 
existsi x, existsi (1:ℤ),
rw (show nat_abs 1 = 1, by norm_num),
exact and.intro hx (nat.coprime_one_right (nat_abs x)),
exfalso, norm_num at h, exfalso, norm_num at h,
end


lemma power_of_minus_one {a : ℤ} : (-1:ℤ)^(nat_abs (a:ℤ)) = (1:ℤ) ↔ a % 2 = 0 := 
begin
split, intro, cases (mod_two_eq_zero_or_one a), exact h,
exfalso,sorry, sorry,
end




lemma descent_step_1 {p k l : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ a b : ℤ, p ∣ (a^2 + 1*b^2) ∧ (nat.coprime (nat_abs a) (nat_abs b))) → (∃ x y : ℤ, p = x^2 + y^2) := 
begin
intro h, cases h with a h, cases h with b h,
have h1 : p ∣ (a-k*p)^2 + (b-l*p)^2, sorry,
have h_k : abs (a-k*p) < p/2, sorry,
have h_l : abs (a-l*p) < p/2, sorry,
have h2 : (a-k*p)^2 + (b-l*p)^2 < p^2, sorry,

sorry,
end

lemma descent_step_2 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b))) → ∃ x y : ℤ, p = x^2 + 2*y^2 := sorry

lemma descent_step_3 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b))) → ∃ x y : ℤ, p = x^2 + 3*y^2 := sorry


lemma reciprocity_step_1 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p): 
p ≡ 1 [ZMOD 4] → ∃ a b : ℤ, (p ∣ (a^2 + 1*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := begin
have h_dvd : ¬ p ∣ 1, 
{
  by_contradiction, 
  have := eq_one_of_dvd_one zero_le_p a, 
  rw this at hp, 
  exact absurd hp.1 nat.not_prime_one,
},
intro h, rw (lemma_4 (show (1:ℤ) ≠ 0, by norm_num) hp h_dvd zero_le_p),
rw [(LQR_supplementary_1 hp zero_le_p), power_of_minus_one], 


sorry,
end

lemma reciprocity_step_2 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p): 
((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) → ∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := sorry

lemma reciprocity_step_3 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2)  (zero_le_p : 0 ≤ p): 
((p = 3) ∨ (p ≡ 1 [ZMOD 3])) → ∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (nat.coprime (nat_abs a) (nat_abs b)) := sorry


--------------- lemmas for theorems 1 2 and 3 ----------------

theorem eq_self_mod {n : ℤ} (x : ℤ) : x ≡ (x % n) [ZMOD n] :=
begin
  show x % n = (x % n) % n,
  rw mod_mod,
end

theorem mod_3_lt_3 (x : ℤ) : 0 ≤ x % 3 ∧ x % 3 < 3 :=
begin
  split,
    exact mod_nonneg x (dec_trivial),
  exact @mod_lt x 3 (dec_trivial),
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

lemma squares_in_mod_2 (d : ℤ) : d * d ≡ 0 [ZMOD 4] ∨ d * d ≡ 1 [ZMOD 4] := begin
have : ∀ d : zmod 4, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ), from dec_trivial,
by have := this d;
  rwa [← cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this,
end

theorem squares_in_mod_3 (x : ℤ) : x ^ 2 ≡ 1 [ZMOD 3] ∨ x ^ 2 ≡ 0 [ZMOD 3] := begin
  have h := mod_lt_3 x, cases h,
  have h1 := modeq.modeq_mul h h,
  rw (show x*x= x^2, by ring) at h1,
  exact or.intro_right (x ^ 2 ≡ 1 [ZMOD 3]) h1,
  cases h, 
  have h1 := modeq.modeq_mul h h,
  rw (show x*x= x^2, by ring) at h1,
  exact or.intro_left (x ^ 2 ≡ 0 [ZMOD 3]) h1,
  have h1 := modeq.modeq_mul h h,
  rw (show x*x= x^2, by ring) at h1, 
  exact or.intro_left (x ^ 2 ≡ 0 [ZMOD 3]) h1,
end


theorem squares_in_mod_8 (d : ℤ) : d * d ≡ 0 [ZMOD 8] ∨ d * d ≡ 1 [ZMOD 8] ∨ d * d ≡ 4 [ZMOD 8] := begin
have : ∀ d : zmod 8, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ) ∨ d * d = (4 : ℤ), from dec_trivial,
by have := this d;
  rwa [← cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this,
end


theorem pos_int_to_nat_abs {a : ℤ} (ha : 0 ≤ a) : 
↑(nat_abs a) = a := begin
have h1:= nat_abs_eq a, cases h1,
exact h1.symm,
have h2 := dec_em (a = 0), cases h2,
rw h2, simp, exfalso,
rw [h1, ←(mul_le_mul_right_of_neg (show (-1:ℤ)<(0:ℤ) , by norm_num))] at ha,
simp at ha,
rw [(show (0 : ℤ)=↑(0 : ℕ), by refl), coe_nat_le, nat.le_zero_iff] at ha,
exact absurd (eq_zero_of_nat_abs_eq_zero ha) h2,
end


lemma prime_int_zero_mod {p n : ℤ} (hp : prime_int p) (hpp : 0 ≤ p) (hn : (2:ℤ) ≤ n) (hpn : ¬ p = n) : 
p ≡ 0 [ZMOD n] → false := begin
intro h,
rw [modeq.modeq_zero_iff, ←dvd_nat_abs, ←nat_abs_dvd, coe_nat_dvd] at h,
unfold prime_int at hp,
have := hp.2 (nat_abs n) h,
cases this,
cases (nat_abs_eq n),
rw [h_1, this] at hn, exact hn,
rw [h_1, this] at hn, exact hn,
cases (nat_abs_eq p), cases (nat_abs_eq n),
rw [h_1, h_2] at hpn, rw ←int.coe_nat_eq_coe_nat_iff at this,
exact absurd this.symm hpn,
rw [this, h_1.symm] at h_2,
unfold nat.prime at hp, 
rw [h_2, ←(mul_le_mul_left_of_neg (show (-1:ℤ)<0, by norm_num))] at hn, simp at hn,
exact le_trans hpp hn,
cases (nat_abs_eq n),
rw [this.symm, h_2.symm] at h_1,
rw [h_1, ←(mul_le_mul_left_of_neg (show (-1:ℤ)<0, by norm_num))] at hpp, simp at hpp,
exact le_trans hn hpp,
rw [this.symm, h_2.symm] at h_1,
exact absurd h_1 hpn,
end

lemma prime_int_even_mod {p a n : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (ha : 2 ∣ a) (hn : 2 ∣ n) :
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


theorem Thm_1 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ x y : ℤ, p = x^2 + y^2) ↔ p ≡ 1 [ZMOD 4] := 
begin
split, intro, cases a with x, cases a_h with y h1,
have h_4 : ¬ p = 4,
{
  by_contradiction, rw a at hp, unfold prime_int at hp, 
  exact absurd hp.1 (show ¬ nat.prime 4, by norm_num),
},
have h_x := squares_in_mod_2 x, ring at h_x,
have h_y := squares_in_mod_2 y, ring at h_y,
cases h_x, cases h_y, 

exfalso,
have h := modeq.modeq_add h_x h_y,
rw h1.symm at h,
exact prime_int_zero_mod hp.1 zero_le_p (show (2:ℤ) ≤ (4:ℤ), by norm_num) h_4 h,

have h := modeq.modeq_add h_x h_y,
rw h1.symm at h, exact h,

cases h_y,
have h := modeq.modeq_add h_x h_y,
rw h1.symm at h,
exact h,

exfalso,
have h := modeq.modeq_add h_x h_y,
rw h1.symm at h, 
exact prime_int_even_mod hp (show (2:ℤ)∣ (1:ℤ) + (1:ℤ), by norm_num) (show (2:ℤ)∣(4:ℤ), by norm_num) h,

-- have h1 := odd_prime_int_is_odd hp,
-- have h_xy : (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0), 
-- begin
--     have h_x := mod_two_eq_zero_or_one x, cases h_x, 
--     have h_y := mod_two_eq_zero_or_one y, cases h_y, 
--     rcases (exists_eq_mul_right_of_dvd ((dvd_iff_mod_eq_zero 2 x).2 h_x)) with m,
--     rw h_1 at h,
--     rcases (exists_eq_mul_right_of_dvd ((dvd_iff_mod_eq_zero 2 y).2 h_y)) with n,
--     rw h_2 at h,
--     rw (show (2 * m) ^ 2 + (2 * n) ^ 2 = 2 * (2*m^2+2*n^2), by ring) at h, 
--     have := dvd_mul_right 2 (2 * m ^ 2 + 2 * n ^ 2), rw h.symm at this,
--     rw dvd_iff_mod_eq_zero at this, rw h1 at this, exfalso, simp at this, exact this,
--     exact or.intro_left (x % 2 = 1 ∧ y % 2 = 0) (and.intro h_x h_y),
--     have h_y := mod_two_eq_zero_or_one y, cases h_y, 
--     exact or.intro_right (x % 2 = 0 ∧ y % 2 = 1) (and.intro h_x h_y),
--     have h2 := modeq.mod_modeq x 2, rw h_x at h2,
--     have h3 := modeq.mod_modeq y 2, rw h_y at h3,
--     have h_5 : ↑(nat_abs 2) = (2:ℤ), by ring,rw h_5 at h2, rw h_5 at h3,
--     rw modeq.modeq_iff_dvd at h2, rw modeq.modeq_iff_dvd at h3,
--     rcases h2 with k, rcases h3 with l,
--     rw ← int_add_sub_r at h2_h, rw ← int_add_sub_r at h3_h,
--     rw [h2_h, h3_h, (show (2 * k + 1) ^ 2 + (2 * l + 1) ^ 2 = 2 * (2*k^2 + 2*k + 2*l^2 + 2*l + 1), by ring)] at h,
--     have := dvd_mul_right 2 (2 * k ^ 2 + 2 * k + 2 * l ^ 2 + 2 * l + 1), rw h.symm at this,
--     rw [dvd_iff_mod_eq_zero, h1] at this, 
--     exfalso, simp at this, exact this,
-- end,
-- cases h_xy,
-- have h_x := modeq.mod_modeq x 2,rw h_xy.1 at h_x,
-- have h_y := modeq.mod_modeq y 2,rw h_xy.2 at h_y,
-- have h_2 : ↑(nat_abs 2) = (2:ℤ), by ring, rw h_2 at h_x, rw h_2 at h_y,
-- rw modeq.modeq_iff_dvd at h_x, rw modeq.modeq_iff_dvd at h_y,
-- cases h_x with k h_x, cases h_y with l h_y, rw ← int_add_sub_r at h_y, simp at h_x,
-- rw [h_x, h_y,(show (2 * k) ^ 2 + (2 * l + 1) ^ 2 = 4 * (k^2 + l^2 +l) +1, by ring)] at h,
-- rw int_add_sub_r at h,
-- have := dvd_mul_right 4 (k ^ 2 + l ^ 2 + l), rw h.symm at this,
-- rw ← modeq.modeq_zero_iff at this, 
-- have h2 := modeq.modeq_add this (show 1 ≡ 1 [ZMOD 4], by refl),
-- simp at h2, exact h2,
-- ---------
-- have h_x := modeq.mod_modeq x 2,rw h_xy.1 at h_x,
-- have h_y := modeq.mod_modeq y 2,rw h_xy.2 at h_y,
-- have h_2 : ↑(nat_abs 2) = (2:ℤ), by ring, rw h_2 at h_x, rw h_2 at h_y,
-- rw modeq.modeq_iff_dvd at h_x, rw modeq.modeq_iff_dvd at h_y,
-- cases h_x with k h_x, cases h_y with l h_y, rw ← int_add_sub_r at h_x, simp at h_y,
-- rw [h_x, h_y,(show (2 * k + 1) ^ 2 + (2 * l) ^ 2 = 4 * (k^2 + l^2 +k) +1, by ring)] at h,
-- rw int_add_sub_r at h,
-- have := dvd_mul_right 4 (k ^ 2 + l ^ 2 + k), rw h.symm at this,
-- rw ← modeq.modeq_zero_iff at this, 
-- have h2 := modeq.modeq_add this (show 1 ≡ 1 [ZMOD 4], by refl),
-- simp at h2, exact h2,
---------

intro ha, exact descent_step_1 hp zero_le_p (reciprocity_step_1 hp zero_le_p ha),
end



theorem Thm_2 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ x y : ℤ, p = x^2 + 2*y^2) ↔ ((p ≡ 1 [ZMOD (8:ℤ)]) ∨ (p ≡ 3 [ZMOD (8:ℤ)])) := 
begin split, intro h,

have h_8 : ¬ p = (8:ℤ), begin
  by_contradiction, rw a at hp, unfold prime_int at hp,
  have : ¬ nat.prime (8:ℕ), by norm_num,
  exact absurd hp.1 this,
end,
rcases h with x, rcases h_h with y,
have h_x := squares_in_mod_8 x, ring at h_x,
have h_y := squares_in_mod_8 y, ring at h_y,
cases h_x, cases h_y, 

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h,
exact prime_int_zero_mod hp.1 zero_le_p (show (2:ℤ) ≤ (8:ℤ), by norm_num) h_8 h,

cases h_y,
exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact prime_int_even_mod hp (show (2:ℤ)∣ (0:ℤ) + (2:ℤ) * (1:ℤ), by simp) (show (2:ℤ)∣(8:ℤ), by norm_num) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
replace h_y := modeq.trans h_y (show 2*4 ≡ 0 [ZMOD (8:ℤ)], by refl),
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h,
exact prime_int_zero_mod hp.1 zero_le_p (show (2:ℤ) ≤ (8:ℤ), by norm_num) h_8 h,

cases h_y, cases h_x,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h,
exact or.intro_left (p ≡ 3 [ZMOD (8:ℤ)]) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact prime_int_even_mod hp (show 2∣ (4:ℤ) + (2:ℤ) * (0:ℤ), by norm_num) (show 2∣(8:ℤ), by norm_num) h,

cases h_x, cases h_y, 
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact or.intro_right (p ≡ 1 [ZMOD (8:ℤ)]) h,

replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact or.intro_left (p ≡ 3 [ZMOD (8:ℤ)]) h,

cases h_y,
exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact prime_int_even_mod hp (show 2∣ (4:ℤ) + (2:ℤ) * (1:ℤ), by norm_num) (show 2∣(8:ℤ), by norm_num) h,

exfalso,
replace h_y := modeq.modeq_mul_left (2:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw h_h_h.symm at h, 
exact prime_int_even_mod hp (show 2∣ (4:ℤ) + (2:ℤ) * (4:ℤ), by norm_num) (show 2∣(8:ℤ), by norm_num) h,

intro ha, exact descent_step_2 hp zero_le_p (reciprocity_step_2 hp zero_le_p ha),
end



theorem Thm_3 {p : ℤ} (hp : prime_int p ∧ nat_abs p ≠ 2) (zero_le_p : 0 ≤ p):
(∃ x y : ℤ, p = x^2 + 3*y^2) ↔ ((p = 3) ∨ (p ≡ 1 [ZMOD 3])) := begin
split, intro ha, 
have h1 := dec_em (p = 3), cases h1,
exact or.intro_left (p ≡ 1 [ZMOD 3]) h1, 
rcases ha with x, rcases ha_h with y,

have h_x := squares_in_mod_3 x,
have h_y := squares_in_mod_3 y,
cases h_x, cases h_y,

replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw ha_h_h.symm at h, 
exact or.intro_right (p = 3) h,

replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw ha_h_h.symm at h, 
exact or.intro_right (p = 3) h,

cases h_y,
exfalso,
replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw ha_h_h.symm at h, 
exact prime_int_zero_mod hp.1 zero_le_p (show (2:ℤ)≤(3:ℤ), by norm_num) h1 h,

exfalso,
replace h_y := modeq.modeq_mul_left (3:ℤ) h_y, 
have h := modeq.modeq_add h_x h_y,
rw ha_h_h.symm at h, 
exact prime_int_zero_mod hp.1 zero_le_p (show (2:ℤ)≤(3:ℤ), by norm_num) h1 h,

intro ha, exact descent_step_3 hp zero_le_p (reciprocity_step_3 hp zero_le_p ha),
end
