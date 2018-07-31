import algebra.group_power

theorem nat.cast_pow {α : Type*} [semiring α] (n : ℕ) : ∀ m : ℕ, (n : α) ^ m = (n ^ m : ℕ)
| 0 := nat.cast_one.symm 
| (d+1) := show ↑n * ↑n ^ d = ↑(n ^ d * n), by rw [nat.cast_pow d,mul_comm,nat.cast_mul]

 theorem nat.pow_two (a : ℕ) : a ^ 2 = a * a := show (1 * a) * a = _, by rw one_mul 
