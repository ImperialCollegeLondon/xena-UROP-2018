import data.nat.gcd
open nat
/-2∗. True or false?
(i) If a and b are positive integers, and there exist integers λ and μ such that λa + μb = 1, then
gcd(a, b) = 1.
(ii) If a and b are positive integers, and there exist integers λ and μ such that λa + μb = 7,
then gcd(a, b) = 7.-/
variables {a b μ ν: ℕ}

--theorem Q0802i (hp: gcd a b = 1) : ∃ μ ν ∧ ν*a +  
