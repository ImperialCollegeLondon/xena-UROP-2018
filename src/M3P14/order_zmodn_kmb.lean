import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 

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

theorem coprime_zmodn_units (n : ℕ) [pos_nat n] : 
equiv (units (zmod n)) {a : zmod n // ∃ b, a * b = 1} :=
{ to_fun := λ u, ⟨u.1, u.2, u.3⟩,
  inv_fun := λ A, 
  { val := (A.val).val, inv := ((A.val).val⁻¹),
    val_inv := by rw [mul_inv_eq_gcd,gcd_one_of_has_inv A.val A.property];dsimp;rw zero_add,
    inv_val := by rw [mul_comm,mul_inv_eq_gcd,gcd_one_of_has_inv A.val A.property];dsimp;rw zero_add,
  },
  left_inv := λ u,begin apply units.ext,show (↑((u.val).val) : zmod n) = u.val,simp,end,
  right_inv := λ A,by simp
}
