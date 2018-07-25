import xenalib.Ellen_Arlt_matrix_rings algebra.module algebra.big_operators data.set.finite analysis.real data.complex.basic algebra.ring 
variable (n:ℕ)
open complex matrix

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
-- def A : matrix ℤ 2 2:= 
-- λ m n,
-- if m=0 ∧ n=0 then 1 else 
-- if m=0 ∧  n=1 then 2 else 
-- if m=1 ∧  n=0 then 3 else
--  4 
#check units


#eval det (1 : matrix ℤ 8 8)

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px
end

def transpose ( R : Type) [ring R] {n:ℕ  }(A:matrix R n n):  matrix R n n:=
λ i j, A j i
def Hermitian_conjugate  [ring ℂ ] {n:ℕ  }(A:matrix ℂ n n):  matrix ℂ n n:=
λ i j, conj (A j i)
def GL (n:ℕ) ( R : Type) [ring R]:= units (matrix R n n)
def Orthogornal: Type:= {A :GL n ℝ   // mul ℝ  A.1 (transpose ℝ A.1)= identity_matrix ℝ  ∧ mul ℝ (transpose ℝ A.1) A.1 = identity_matrix ℝ  }
def Hermitian : Type:= {A :matrix ℂ n n //  mul ℂ A (Hermitian_conjugate A)= (1 : matrix ℂ n n)}
theorem transpose_of_product ( R : Type) [comm_ring R] {n:ℕ}(A B:matrix R n n): transpose R (mul R A B) = mul R (transpose R B) (transpose R A) := 
begin
unfold mul,
unfold transpose,
simp[mul_comm],
end 
instance GL_group (n:ℕ ) ( R : Type) [ring R]:group (GL n R):=
begin
unfold GL,
apply_instance,
end 








