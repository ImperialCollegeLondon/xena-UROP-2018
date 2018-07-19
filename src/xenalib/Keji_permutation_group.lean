import xenalib.Group_actions data.fintype data.set.finite data.equiv xenalib.Ellen_Arlt_matrix_rings algebra.big_operators data.set.finite group_theory.coset
local attribute [instance] classical.prop_decidable

noncomputable instance {n : ℕ} : fintype {f : fin n→ fin n // function.bijective f}  := 
set_fintype _
def S (n: ℕ ) := equiv.perm (fin n)
instance (n : ℕ) : has_coe_to_fun (S n) := by unfold S; apply_instance


noncomputable instance Sn_finite {n:ℕ}: fintype (S n):=
fintype.of_surjective 
(λ (f : {f : fin n → fin n // function.bijective f}), equiv.of_bijective f.2) 
begin 
unfold function.surjective,
simp,
intro b,
let f:{f : fin n → fin n // function.bijective f}:=  ⟨ b.1,b.bijective⟩,
existsi f.1,
existsi  f.2,
apply equiv.ext,
intro x,
rw equiv.of_bijective_to_fun,
refl,
end
instance g (n : ℕ) : is_group_action (equiv.to_fun : S n → fin n → fin n) :=
{ one := λ _, rfl,
  mul := λ _ _ _, rfl }

open is_group_action
theorem Sn_transitive {n:ℕ}(i:fin n): ∀ (j:fin n), j ∈ is_group_action.orbit equiv.to_fun i:=
begin 
intro j,
unfold is_group_action.orbit,
unfold set.range,
simp,
let f := λx, if x=i then j else if x=j then i else x,
refine exists.intro ⟨ f,f, λ _, begin
 simp [f]; split_ifs; simp*,
  end,
  λ _, begin simp [f]; split_ifs; simp*, 
  end⟩ _, 
simp,
simp[f],
split_ifs,
refl,
refl,
end 
variables (n:ℕ) 
def f' {n:ℕ }(f:is_group_action.stabilizer (equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩): fin n → fin n := 
λ x, ⟨(f.1.1 (fin.raise x)).1,
begin
  have : ((f.val).to_fun ⟨n, nat.lt_succ_self n⟩).val = n := fin.veq_of_eq f.2,
  refine lt_of_le_of_ne _ _,
  exact (nat.le_of_lt_succ (f.1.1 (fin.raise x)).2),
  assume h,
  conv at h {to_rhs, rw ← this},
  have h : x.val = n := fin.veq_of_eq (f.1.bijective.1 (fin.eq_of_veq h)),
  have : x.val < n := x.2,
  simpa[lt_irrefl, h] using this,
end⟩
theorem f'_bijecive {n:ℕ }(f:is_group_action.stabilizer (equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩): function.bijective(f' f):=
begin 
unfold function.bijective,
split,
unfold function.injective,
intros,
rw[f'] at a,
have H1: ((f.val).to_fun (fin.raise a₁)).val =
     ((f.val).to_fun (fin.raise a₂)).val,
rw[ fin.veq_of_eq a],
have H2 : (fin.raise a₁).val = (fin.raise a₂).val,
exact fin.veq_of_eq (f.1.bijective.1 (fin.eq_of_veq H1)),
exact fin.eq_of_veq H2,
unfold function.surjective,
intros,
unfold f',
existsi ⟨(f.val⁻¹ (fin.raise b)).val, begin end⟩ 








end 
def F : is_group_action.stabilizer (equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩ → S n:=
λ f, ⟨ (f' f),λ x, ⟨(f.1.2 (fin.raise x)).1,
begin
have H1: f.val⁻¹ ∈  stabilizer 
(equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩,
rw[is_subgroup.inv_mem_iff],
exact f.2,
 have : ((f.val⁻¹).to_fun ⟨n, nat.lt_succ_self n⟩).val = n := 
 fin.veq_of_eq H1,
 refine lt_of_le_of_ne _ _,
  exact (nat.le_of_lt_succ (f.1.2 (fin.raise x)).2),
  assume h,
  conv at h {to_rhs, rw ← this},
  have h : x.val = n := fin.veq_of_eq ((f.val⁻¹).bijective.1 (fin.eq_of_veq h)),
  have : x.val < n := x.2,
  simpa[lt_irrefl, h] using this,
  
end⟩, begin 
intro x,
refine fin.eq_of_veq _,
--dsimp[fin.raise],
end ,sorry⟩  


theorem mag_S {n:ℕ}: fintype.card (S n) = nat.fact n := sorry
