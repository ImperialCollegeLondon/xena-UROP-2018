import data.nat.gcd data.nat.prime algebra.group_power 
open nat
-- set option class.instance_max_depth
/- 
4. (i) Say a and b are coprime positive integers, and N is any integer which is a multiple of a and of b. Prove that N is a multiple of a*b. Hint: we know that λa+μb = 1 for some λ,μ ∈ Z; now write N = N × (λa + μb).

(ii) By applying (i) twice, deduce that if p, q and r are three distinct primes, then two integers x and y are congruent modulo pqr if and only if they are congruent mod p, mod q and mod r.

(iii) (tough) Consider the set of positive integers {27 − 2, 37 − 3, 47 − 4, . . . , 10007 − 1000}. What is the greatest common divisor of all the elements of this set? Feel free to use a calculator to get the hang of this; feel free to use Fermat’s Little Theorem and the previous part to nail it.

(iv) (tougher) 561 = 3×11×17. Prove that if n ∈ Z then n561 ≡ n mod 561. Hence the converse to Fermat’s Little Theorem is false.-/
variables {a b p q r : ℕ}
variables {N x y n : ℤ}

theorem Q0805i (hp : gcd a b = 1) (hq : a ∣ N ∧ b ∣ N) : a*b ∣ N := sorry 

-- is there a slicker way to write this?

--theorem Q0805ii (hp : prime p ∧ prime q ∧ prime r) (hq : p ≠ q ≠ r) : x % p*q*r = y ↔ (x % p = y) ∧ (x % q = y) ∧ (x % r = y)

--theorem Q0805iii 

--theorem Q0805iv : n^(561) % 561 = n := sorry 

-- the converse to fermat's little theorem is false!

--theorem Q0805iv_cor  : (x^p % p = 1 → prime p) → ff := sorry
