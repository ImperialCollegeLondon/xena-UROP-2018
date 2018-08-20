import algebra.big_operators algebra.group_power chris_hughes_various.zmod data.fintype data.nat.gcd M3P14.order_zmodn_kmb M3P14.Arithmetic_functions.mobius

open nat 
open fintype

--TODO: Add explicit formula for τ n 
-- make the non-computable definition of mobius function work
-- add the mobius inversion formula

-- arithmetic functions and their properties

def is_mult (f : ℕ → ℕ) (m n : ℕ) (hp: gcd m n = 1) := f (m * n) = (f m) * (f n)
def is_strong_mult (f : ℕ → ℕ) (m n : ℕ) := f (m * n) = (f m) * (f n)
def is_add (f : ℕ → ℤ) (m n : ℕ) (hp: gcd m n = 1) := f (m + n) = (f m) + (f n)
def is_strong_add (f : ℕ → ℤ) (m n : ℕ) := f (m + n) = (f m) + (f n)

-- minor arithmetic functions that nobody cares about probably

--liouville function

def liouville_function (n : ℕ) : int := (-1)^(primes_div_dup n) 
local notation `δ` := liouville_function
-- lambda was already taken up by lambda functions
theorem lio_strong_mul (n m : ℕ) : δ (m * n) = (δ m) * (δ n) := sorry 

--number of divisors

def number_of_divisors_function (n : ℕ) := n.factors.erase_dup.length
local notation `τ` := number_of_divisors_function

theorem tau_is_mul (n m : ℕ) (hp: gcd n m = 1) : τ (n*m) = (τ n) * (τ m) := sorry 

--theorem tau_formula (n α : ℕ) 
    -- ((range n.succ).filter (∣ n))
