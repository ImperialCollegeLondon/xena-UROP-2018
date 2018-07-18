import group_theory.subgroup data.set.basic algebra.group data.equiv

-- sheet 5
variables {G : Type*} [group G]
variables (H K : set G)
variables [is_subgroup H] [is_subgroup K]

-- 1. Recall that for a matrix A = (aij), the transpose of A is the matrix AT = (bij), where bij = aji. Let G = GL(2,R), and let H ⊆ G be the subset
-- H ={A∈G|ATA=I}.
-- (a) Show that H is a subgroup of G.
-- (b) What are the possible determinants for an element of H?
-- (c) Show that the elements of H with determinant 1 form a subgroup K of
-- G.
-- (d) Prove that, with K as in (c):
-- 􏰄􏰂cosθ −sinθ􏰃 􏰅 K = sin θ cos θ : θ ∈ R
-- .
-- (e) Find an element of H of order 3, and another with infinite order.
-- (f) Show that K is abelian. Is H abelian?
-- (g) Generalize parts (a), (b), (c).

-- 2∗. Which of the following subsets H are subgroups of the given group G?
-- (a) G=(Z,+),H={n∈Z|n≡0mod37}.
-- (b) G=GL(2,C),H={A∈G|A2 =I}.
-- (c) G=GL(2,R),H={A∈G|det(A)=1}.
-- (d) G=Sn,H={g∈G|g(1)=1}(forn∈N).
-- (e) G=Sn,H={g∈G|g(1)=2}.
-- (f) G=Sn,H isthesetofallpermutationsg∈Gsuchthat g(i) − g(j) ≡ i − j mod n for all i, j ∈ {1, . . . , n}.

-- 3. Let G be a group with subgroups H and K.
-- (a) Prove that H ∩ K is a subgroup of G.
theorem sheet05_q3a: is_subgroup(H ∩ K) := sorry
-- (b) Show that H ∪ K is not a subgroup, unless either H ⊆ K or K ⊆ H.
theorem sheet05_q3b (hp:¬(H ⊆ K ∨ K ⊆ H)): ¬is_subgroup(H ∪ K) := sorry

-- 4. Prove the following statements.
definition is_cyclic (G : Type*) [group G] := ∃ x : G, gpowers x = set.univ
-- (a) Every cyclic group is abelian.
theorem sheet05_q4a : is_cyclic G → comm_group G := sorry
--{ ..is_subgrou }
definition gsymmetric (n : ℕ) := equiv.perm (fin n)
-- (b) The symmetric group is not abelian, unless n < 3.
theorem sheet05_q4b (n : ℕ) (n < 3) : comm_group (gsymmetric n) → gsymmetric n := sorry 

-- 5. Find an example of each of the following:
-- (a) an element of order 3 in the group GL(2, C).
-- (b) an element of order 3 in the group GL(2, R).
-- (c) an element of infinite order in the group GL(2, R). (d) an element of order 12 in the group S7.

-- 6. Let G=S₅.
-- (a) Show that any element of G which fixes exactly two points in {1, 2, 3, 4, 5}
-- must have order 3.
-- (b) What are the possible orders of a cyclic subgroup of G?
-- (c) Find a proper subgroup of G which is not cyclic.

-- 7. Which of the following groups are cyclic?
-- (a) S2.
-- (b) GL(2,R).􏰄􏰂a 0􏰃
-- (c) 0 b |
-- (d) (Q,+). a, b ∈ {1, −1}
-- under matrix multiplication.