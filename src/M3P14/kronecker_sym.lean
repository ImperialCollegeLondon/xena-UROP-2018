/- Generalisation of the Jacobi symbol which is itself a generalisation of the Legendre symbol 

ROADMAP:
    - Write the mathematical definition of the Kronecker symbol
    - Write the algorithm that computes any kronecker symbol a b
    - Prove the 2 above definitions are equal
    - Prove the relationship between the Jacobi symbol and the Kronecker symbol
    - Prove the relationship between the Legendre symbol and the Kronecker symbol
    - Write all the properties
-/

import data.nat.basic M3P14.order_zmodn_kmb data.int.basic M3P14.lqr data.nat.prime M3P14.jacobi_sym

def kronecker_sym_algorithm : ℤ → ℤ → ℤ
| a          b := 0

noncomputable def kronecker_sym (a b : ℤ) := 0

local notation ((a|b)) := kronecker_sym_algorithm a b 

#eval ((8|1))

theorem kronecker_def_eq (a b : ℤ) : kronecker_sym_algorithm a b = kronecker_sym a b := sorry

theorem kronecker_generelises_jacobi {n : ℤ} (a : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) : kronecker_sym a n = jacobi_symbol a hn := sorry
