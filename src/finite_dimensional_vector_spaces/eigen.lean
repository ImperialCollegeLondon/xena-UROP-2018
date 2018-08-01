import .linear_map
import xenalib.Ellen_Arlt_matrix_rings

-- eigenvalue and eigenvector
namespace eigen

variables {k : Type} (V : Type*)
variables [field k] [vector_space k V] [module k V]

def is_eigenvalue (T : linear_map V V) (a : k) :=
∃ v : V , (v ≠ (0 : V)) ∧ (T v = a • v)

def is_eigenvector (T : linear_map V V) (v : V) (h : v ≠ (0 : V)) :=
∃ a : k, T v = a • v


-- Suppose V is a f.d.v.s, and B = {v1,...,vn} is a vasis of V. Let T : V → V be a linear map.
-- i The eigenvalues of T are exactly the same as the eigenvalues of [T]B.
-- ii The eigenvectors of T are those v ∈ V such that [v]B is an eigenvector of [T]B.
open vector_space
-- theorem eigen_equil_one (T : linear_map V V)  (b : vector_space.linear_map_to_vec):= sorry

-- Proposition 7.5. Suppose V is a f.d.v.s, and B = {v1, ..., vn} is a basis. Suppose T : V → V is a linear map. Then,
-- [T]B isdiagonal⇔v1,...,vn areeigenvectorsofT

-- Definition 7.6. If V is a f.d.v.s, and T : V → V is a linear map, say that T is diagonalisable if
-- there a basis of V consisting of eigenvectors of V .



-- Corollary 7.7. Suppose V is a f.d.v.s. with a basis B = {v1, ..., vn}. Suppose T : V → V is a
-- linear map. Then the following are equivalent: i T is diagonalisable
-- ii There is a basis C of V with [T]C is diagonal
-- iii There is an invertible n×n matrix P with P−1[T]BP a diagonal matrix
end eigen