import group_theory.subgroup data.set.basic algebra.group data.equiv

-- sheet 5
variables {G : Type*} [group G]
variables (H K : set G)
variables [is_subgroup H] [is_subgroup K]

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
--theorem sheet05_q4b (n : ℕ) (n ≥ 4) : gsymmetric n → ¬(comm_group (gsymmetric n)) := sorry 
