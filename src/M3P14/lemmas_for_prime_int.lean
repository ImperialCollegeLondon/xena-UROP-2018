import data.int.basic
import data.int.modeq
import data.int.order
import algebra.group_power
import tactic.ring
open nat 

--#check int.le
--theorem l_to_le {a b : ℤ} (hab : a < b) : a ≤ b := begin
--unfold has_le.le,
--unfold int.le,
--have h1 : b < b+1, by lt_succ_self b, 
--end


definition is_sum_of_two_squares (n : ℕ) := ∃ x y : ℤ, (n : ℤ) =  x ^ 2 + y ^ 2


theorem is_sum_of_two_squares_mul (m n : ℕ) : is_sum_of_two_squares m ∧ is_sum_of_two_squares n → is_sum_of_two_squares (m * n) := 
begin
intro h,
unfold is_sum_of_two_squares,
unfold is_sum_of_two_squares at h, 
rcases h with ⟨⟨a, b, hab⟩, ⟨c, d, hcd⟩⟩,
existsi [a * c - b * d, a * d + b * c],
rw int.coe_nat_mul, rw hab, rw hcd, 
ring,


--have h2 : is_sum_of_two_squares m, from h.1,
--unfold is_sum_of_two_squares at h2,
--conv at h in (is_sum_of_two_squares m )
--begin
--unfold is_sum_of_two_squares
--end

end 


--inductive less_than_or_equal (a : ℤ) : ℤ → Prop
--| refl : less_than_or_equal a
--| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

--def le_refl : ∀ a : ℤ, a ≤ a :=
--less_than_or_equal.refl


--lemma le_succ (n:ℤ) : n ≤ succ n :=
--less_than_or_equal.step (int.le_refl n)


--theorem le_of_succ_le {n m : ℤ} (h : succ n ≤ m) : n ≤ m := 
--int.le_trans (le_succ n) h