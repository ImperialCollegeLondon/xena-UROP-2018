import algebra.big_operators data.set.finite

def matrix (α : Type*) (m n : ℕ) := fin m → fin n → α

namespace matrix
variables {α : Type*} [ring α]
variables {l m n o : ℕ}

instance : has_zero (matrix α m n) :=
⟨λ _ _, 0⟩

instance : has_neg (matrix α m n) :=
⟨λ M x y, - M x y⟩

instance : has_add (matrix α m n) :=
⟨λ M N x y, M x y + N x y⟩

@[simp] theorem add_val {M N : matrix α m n} {x : fin m} {y : fin n} : (M + N) x y = M x y + N x y :=
rfl

theorem add_assoc (L : matrix α m n) (M : matrix α m n) (N : matrix α m n) :
  L + (M + N) = (L + M) + N :=
funext $ λ x, funext $ λ y, by simp

def mul (M : matrix α l m) (N : matrix α m n) : matrix α l n :=
λ x z, finset.univ.sum (λ y, M x y * N y z)

@[simp] theorem mul_val {M : matrix α l m} {N : matrix α m n} {x : fin l} {z : fin n} :
  (M.mul N) x z = finset.univ.sum (λ y, M x y * N y z) :=
rfl

theorem mul_assoc (L : matrix α l m) (M : matrix α m n) (N : matrix α n o) :
  L.mul (M.mul N) = (L.mul M).mul N :=
funext $ λ x, funext $ λ z,
  calc finset.univ.sum (λ (y₁ : fin m), L x y₁ * finset.univ.sum (λ (y₂ : fin n), M y₁ y₂ * N y₂ z))
    = finset.univ.sum (λ (y₁ : fin m), finset.univ.sum (λ (y₂ : fin n), L x y₁ * M y₁ y₂ * N y₂ z)) :
      by congr; funext; rw finset.mul_sum; congr; funext; rw mul_assoc
    ... = finset.univ.sum (λ (y₂ : fin n), finset.univ.sum (λ (y₁ : fin m), L x y₁ * M y₁ y₂ * N y₂ z)) :
      by rw finset.sum_comm
    ... = finset.univ.sum (λ (y₂ : fin n), finset.univ.sum (λ (y₁ : fin m), L x y₁ * M y₁ y₂) * N y₂ z) :
      by congr; funext; rw ←finset.sum_mul

end matrix
