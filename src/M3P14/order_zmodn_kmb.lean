import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

open zmod nat

-- I spell this one out so you can see how it goes.
lemma gcd_one_of_unit {n : ℕ} [pos_nat n] (u : units (zmod n)) :
nat.gcd (u.val.val) n = 1 :=
begin
  let abar := u.val, let bbar := u.inv, --  in zmod n
  let a := abar.val, let b := bbar.val, -- in ℕ
  have H : (a * b) % n = 1 % n,
    show (abar.val * bbar.val) % n = 1 % n,
    rw ←mul_val,
    rw u.val_inv,
    refl,
  let d := nat.gcd a n,
  show d = 1,
  rw ←nat.dvd_one,
  rw ←dvd_mod_iff (gcd_dvd_right a n),
  rw ←H,
  rw dvd_mod_iff (gcd_dvd_right a n),
  apply dvd_mul_of_dvd_left,
  exact gcd_dvd_left a n
end

-- this one comes for free now, and it's the one we want
lemma gcd_one_of_has_inv {n : ℕ} [pos_nat n] (a : zmod n) (Hinv : ∃ b, a * b = 1) :
nat.gcd (a.val) n = 1 :=
begin
  cases Hinv with b Hb,
  let u : units (zmod n) := ⟨a,b,Hb,mul_comm a b ▸ Hb⟩,
  exact gcd_one_of_unit u
end 

-- thanks Chris :-)
@[simp] lemma cast_val {n : ℕ} [pos_nat n] (a : zmod n) : (a.val : zmod n) = a :=
by cases a; simp [mk_eq_cast]

def coprime_zmodn_units (n : ℕ) [pos_nat n] : 
equiv (units (zmod n)) {a : zmod n // ∃ b, a * b = 1} :=
{ to_fun := λ u, ⟨u.1, u.2, u.3⟩,
  inv_fun := λ A, 
  { val := (A.val).val, inv := ((A.val).val⁻¹),
    val_inv := by rw [mul_inv_eq_gcd,gcd_one_of_has_inv A.val A.property];dsimp;rw zero_add,
    inv_val := by rw [mul_comm,mul_inv_eq_gcd,gcd_one_of_has_inv A.val A.property];dsimp;rw zero_add,
  },
  left_inv := λ u,begin apply units.ext,show (↑((u.val).val) : zmod n) = u.val,simp,end,
  right_inv := λ A, by simp
}

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance (n : ℕ) [pos_nat n] : fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))
instance (n : ℕ) [pos_nat n] : decidable_eq (units (zmod n)) :=  λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩
 
def order_of_zmod (a n : ℕ) [pos_nat n] : ℕ := @order_of (units (zmod n)) _ _ _ ⟨a, a⁻¹, sorry, sorry⟩ 

#eval order_of_zmod 2 7

theorem exists_pow_eq_one_mod_n (a n : ℕ) : ∃i≠0, a ^ i ≡ 1 [MOD n] := sorry

theorem order_div (a n d : ℕ) (h : coprime a n) [pos_nat n] : a^d ≡ 1 [MOD n] → (order_of_zmod a n) ∣ d := 
begin
  intro h,
  unfold order_of_zmod,
  unfold order_of,
  sorry
end

/-
theorem order_div_phi_n (a n : ℕ) (h : coprime a n) : order_of_zmod (a : zmod n) ∣ phi n := sorry

theorem pow_order_eq_one (a n : ℕ) (h: coprime a n) : a ^ order_of_zmod (a : zmod n) ≡ 1 [MOD n] := sorry

def primitive_root (a n : ℕ) := coprime a n ∧ order_of_zmod (a : zmod n) = phi n

theorem primitive_root_existence (n : ℕ) : ∃ a : ℕ, (primitive_root a n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p r : ℕ, prime p ∧ r > 0 → (n = p^r ∨ n = 2*p^r) := sorry
-/