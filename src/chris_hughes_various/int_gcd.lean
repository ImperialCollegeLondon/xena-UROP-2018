import data.int.basic data.nat.gcd

namespace int

lemma dvd_mod_iff {k m n : ℤ} (h : k ∣ n) : k ∣ m % n ↔ k ∣ m :=
let t := @dvd_add_iff_left _ _ _ (m % n) _ (dvd_trans h (dvd_mul_right n (m / n))) in
by rwa mod_add_div at t

@[simp] lemma gcd_zero_left (a : ℤ) : gcd 0 a = a.nat_abs := nat.gcd_zero_left _

@[simp] lemma  gcd_zero_right (a : ℤ) : gcd a 0 = a.nat_abs := nat.gcd_zero_right _

@[simp] lemma gcd_one_left (a : ℤ) : gcd 1 a = 1 := nat.gcd_one_left _

@[simp] lemma gcd_one_right (a : ℤ) : gcd a 1 = 1 := nat.gcd_one_right _

lemma gcd_comm (a b : ℤ) : gcd a b = gcd b a := nat.gcd_comm _ _

lemma gcd_mul_left (a b c : ℤ) : gcd (a * b) (a * c) = a.nat_abs * gcd b c := 
by unfold gcd;
  rw [nat_abs_mul, nat_abs_mul, nat.gcd_mul_left]

lemma gcd_mul_right (a b c : ℤ) : gcd (b * a) (c * a) = gcd b c * a.nat_abs :=
by rw [mul_comm b, mul_comm c, gcd_mul_left, mul_comm (gcd b c)]

lemma gcd_pos_of_ne_zero_left {a : ℤ} (b : ℤ) (hb : b ≠ 0) : 0 < gcd a b :=
by unfold gcd; exact nat.gcd_pos_of_pos_right _ (nat_abs_pos_of_ne_zero hb)

@[simp] lemma gcd_neg (a b : ℤ) : gcd (-a) b = gcd a b :=
by unfold gcd; rw nat_abs_neg

@[simp] lemma gcd_neg' (a b : ℤ) : gcd a (-b) = gcd a b :=
by unfold gcd; rw nat_abs_neg

lemma gcd_dvd_left (a b : ℤ) : (gcd a b : ℤ) ∣ a :=
dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ nat.gcd_dvd_left _ _

lemma gcd_dvd_right (a b : ℤ) : (gcd a b : ℤ) ∣ b :=
dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ nat.gcd_dvd_right _ _ 

lemma dvd_gcd {a b c : ℤ} (hb : a ∣ b) (hc : a ∣ c) : a ∣ gcd b c :=
nat_abs_dvd.1 $ int.coe_nat_dvd.2 (begin
  rw [← nat_abs_dvd, ← dvd_nat_abs, int.coe_nat_dvd] at hb hc,
  exact nat.dvd_gcd hb hc
end)

lemma gcd_mod (a b : ℤ) : gcd (b % a) a = gcd a b:=
nat.dvd_antisymm
  (int.coe_nat_dvd.1 (dvd_gcd (gcd_dvd_right (b % a) a) 
    ((dvd_mod_iff (gcd_dvd_right (b % a) a)).1 (gcd_dvd_left (b % a) a))))
  (int.coe_nat_dvd.1 (dvd_gcd ((dvd_mod_iff (gcd_dvd_left a b)).2 
    (gcd_dvd_right a b)) (gcd_dvd_left a b)))

lemma gcd_assoc (a b c : ℤ) : gcd (gcd a b) c = gcd a (gcd b c) := nat.gcd_assoc _ _ _

end int