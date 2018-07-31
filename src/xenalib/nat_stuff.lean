import algebra.group_power
import data.nat.basic data.nat.cast

#check nat.mul


theorem nat.cast_pow {α : Type*} [semiring α] (n : ℕ) : ∀ m : ℕ, (n : α) ^ m = (n ^ m : ℕ)
| 0 := nat.cast_one.symm 
| (d+1) := show ↑n * ↑n ^ d = ↑(n ^ d * n), by rw [nat.cast_pow d,mul_comm,nat.cast_mul]

theorem int.cast_pow {α : Type*} [ring α] (n : ℤ) : ∀ m : ℕ, (n : α) ^ m = (n ^ m : ℤ)
| 0 := nat.cast_one.symm 
| (d+1) := show ↑n * ↑n ^ d = ↑(n * n ^ d), by rw [int.cast_pow d,int.cast_mul]

theorem nat.cast_pow' (n : ℕ) : ∀ m : ℕ, (n : ℤ) ^ m = (n ^ m : ℕ)
| 0 := nat.cast_one.symm 
| (d+1) := show ↑n * ↑n ^ d = ↑(n ^ d * n),
-- by rw [nat.cast_pow' d,mul_comm,nat.cast_mul]
begin
rw nat.cast_pow' d,
rw mul_comm,
simp,
end 

theorem nat.pow_pow (n a : ℕ) : ∀ b : ℕ, (n ^ a) ^ b = n ^ (a * b)
| 0 := by rw mul_zero;refl
| (d+1) := show (n^a)^d * n^a = _, by rw [mul_add,mul_one,nat.pow_add,nat.pow_pow]

theorem nat.mul_div {a b : ℕ} : a ≠ 0 → a ∣ b → a * (b / a) = b :=
begin
  intros Ha Hd,
  rw nat.dvd_iff_mod_eq_zero at Hd,
  exact zero_add (a * (b / a)) ▸ (Hd ▸ nat.mod_add_div b a)
end 

theorem nat.pow_two (a : ℕ) : a ^ 2 = a * a := show (1 * a) * a = _, by rw one_mul 
