import xenalib.Ellen_Arlt_matrix_rings algebra.big_operators data.set.finite
def Cross_out_column {R : Type} [ring R] {n : nat }
  (A:matrix R (n+1) (n+1)) (m :fin (n+1)): matrix R n n := 
λ i j,
if j.1 < m.1 then  A (i.1+1) j.1 else 
  A (i.1+1) (j.1+1) 
def det {R : Type} [ring R]: Π {n: nat},  matrix R (n+1) (n+1) →  R
| 0 := λ A, A 0 0
| (n + 1) := λ A, 
  finset.sum finset.univ (λ k : fin (n+2), (-1: R)^(k.1) *(A 0 k) *
 det (Cross_out_column A k))
def A : matrix ℤ 2 2:= 
λ m n,
if m=0 ∧ n=0 then 1 else 
if m=0 ∧  n=1 then 2 else 
if m=1 ∧  n=0 then 3 else
 4 


#eval det (1 : matrix ℤ 8 8)

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px
end