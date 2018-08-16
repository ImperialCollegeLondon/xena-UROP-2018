import data.nat.prime algebra.big_operators M3P14.Arithmetic_functions.sum_over_divisors

open nat 

-- mobius function

-- taken from M3P14 sheet 1
def square_free_int (n : ℕ) := ∀ p : ℕ, prime p ∧ (p ∣ n → ¬ (p^2 ∣ n))

-- number of prime divisors of n, not counting multiplicities
def primes_div_no_mult (n : ℕ) := n.factors.erase_dup.length
local notation `ω` := primes_div_no_mult
--#eval ω 30

--number of prime divisors of n, counting multiplicities
def primes_div_mult (n : ℕ) := n.factors.length
local notation `Ω` := primes_div_mult
--#eval Ω 300

local attribute [instance] classical.prop_decidable

noncomputable def mobius (n : ℕ) : int := 
if square_free_int n ∧ (2 ∣ ω n) then 1 else 
if square_free_int n ∧ ¬(2 ∣ ω n) then -1 
else 0

local notation `μ`  := mobius

theorem mob_mul (m n : ℕ) : μ (m*n) = (μ m ) * (μ n) := sorry

lemma non_coprime (m n : ℕ) : (gcd m n) > 1 → μ (m * n) = 0 := sorry

--theorem mob_sum (n d : ℕ) (hp : n ≠ 1) (hq: d ∣ n) : divisor_sum mobius n = 0 := sorry

--def mertens_func (n k : ℕ) := sum k μ n 

--theorem mobius_inv (m n : ℕ) (f : ℕ → ℕ) (g : ℕ → ℕ) : (g n = sum f d) → (f n = sum (μ d) * g (n / d) ) := sorry 
 