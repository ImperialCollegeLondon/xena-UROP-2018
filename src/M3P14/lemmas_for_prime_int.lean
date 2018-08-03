import data.int.basic
import data.int.modeq
import data.int.order

open int

#check int.le
theorem l_to_le {a b : ℤ} (hab : a < b) : a ≤ b := begin
unfold has_le.le,
unfold int.le,
have h1 : b < b+1, by lt_succ_self b, 
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