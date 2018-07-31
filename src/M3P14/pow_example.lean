-- UNFINISHED -- WORK IN PROGRESS. KMB

import xenalib.nat_stuff
import chris_hughes_various.zmod

/- Here is my memory of the situation Clara and Jason were faced with -/
set_option pp.all true
example (a : ℕ) (p : ℕ) (x : ℤ) 
  (H1 : ↑(a ^ (p - 1)) - 1 ≡ 0 [ZMOD ↑p]) 
  (H2 : x ≡ (↑a)^2 [ZMOD ↑p]) :
x ^ ((p-1) / 2) ≡ 1 [ZMOD ↑p] :=
-- A mathematician would just say "substitute x = a^2 and we're done"
-- Lean says "naturals aren't integers, and congruence is not equality, so no"
-- I say "that's OK, we just explain to Lean that things which are "obviously equal" are equal"
begin
  rw @nat.cast_pow ℤ _ a 2 at H2,
end 
