import analysis.real data.nat.prime algebra.big_operators

open nat 

-- taken from M3P14 sheet 1
def square_free_int (n : ℕ) := ∀ p : ℕ, prime p ∧ (p ∣ n → ¬ (p^2 ∣ n))

--instance : decidable_pred square_free_int := 
--λ n, by unfold square_free_int; apply_instance

def primes_div_n (n : ℕ) := n.factors.erase_dup.length
--#eval primes_div_n 30

local attribute [instance] classical.prop_decidable

noncomputable def mobius (n : ℕ) : int := 
if square_free_int n ∧ (2 ∣ primes_div_n n) then 1 else 
if square_free_int n ∧ ¬(2 ∣ primes_div_n n) then -1 
else 0

local notation `μ`  := mobius

--theorem mob_mul (m n : ℕ) : μ (m*n) = (μ m ) * (μ n) := sorry

--lemma non_coprime (m n : ℕ) : (gcd m n) > 1 → μ (m * n) = 0 := sorry

--theorem mob_sum (n d : ℕ) (hp : n ≠ 1) (hq: d ∣ n) : sum (d μ n) = 0 := sorry

--def mertens_func (n k : ℕ) := sum k μ n 

--theorem mobius_inv (m n : ℕ) (f : ℕ → ℕ) (g : ℕ → ℕ) : (g n = sum f d) → (f n = sum (μ d) * g (n / d) ) := sorry 