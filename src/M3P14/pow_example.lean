import xenalib.nat_stuff
import chris_hughes_various.zmod

/- Here is my memory of the situation Clara and Jason were faced with -/
--set_option pp.all true
--set_option pp.notation false
example (a : ℕ) (p : ℕ) [pos_nat p] (Hodd : 2 ∣ (p - 1)) (x : ℤ) 
  (H1 : ↑(a ^ (p - 1)) - 1 ≡ 0 [ZMOD ↑p]) 
  (H2 : x ≡ (↑a)^2 [ZMOD ↑p]) :
x ^ ((p-1) / 2) ≡ 1 [ZMOD ↑p] :=
-- A mathematician would just say "substitute x = a^2 and we're done"
-- Lean says "naturals aren't integers, and congruence is not equality, so no"
-- I say "that's OK, we just explain to Lean exactly why things which are
-- "obviously equal" are equal"
begin
  rw nat.cast_pow' a 2 at H2,
  rw ←zmod.eq_iff_modeq_int at H2,
  -- H2 now an equality in the ring Z/pZ
  rw ←zmod.eq_iff_modeq_int,
  rw ←int.cast_pow,
  -- we can finally rewrite!
  rw H2,
  -- we now have to convince Lean that this is just H1
  rw int.cast_pow,
  rw nat.cast_pow',
  rw nat.pow_pow,
  rw nat.mul_div (show 2 ≠ 0, from dec_trivial) Hodd,
  apply eq_of_sub_eq_zero,
  rw ←int.cast_sub,
  rw ←zmod.eq_iff_modeq_int at H1,
  exact H1
end 
