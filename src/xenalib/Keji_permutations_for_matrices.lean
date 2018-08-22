import data.fintype data.set.finite data.equiv.basic xenalib.Ellen_Arlt_matrix_rings algebra.big_operators data.set.finite group_theory.coset algebra.group
import group_theory.perm
open fintype 
noncomputable instance bij_fintype {n : ℕ} : fintype {f : fin n→ fin n // function.bijective f}  := 
set_fintype _
noncomputable instance equiv_perm_fin_finite {n:ℕ}: fintype (equiv.perm(fin n)):=
fintype.of_surjective (λ (f : {f : fin n → fin n // function.bijective f}), equiv.of_bijective f.2) 
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

def e {n:ℕ} {R:Type} [comm_ring R] (σ :  equiv.perm (fin n)) : R:= ((equiv.perm.sign σ : ℤ ): R)
theorem sig_eq_inv {n:ℕ} (π: equiv.perm (fin n))  : equiv.perm.sign(π ) = equiv.perm.sign(π.symm ) := 
begin 
{rw[eq_comm],
show equiv.perm.sign (π⁻¹  ) = equiv.perm.sign π,
rw[ is_group_hom.inv equiv.perm.sign] ,
swap,
apply_instance,
have h1: ∀ i: units ℤ ,  i⁻¹ = i,
exact dec_trivial,
rw[h1],}
end
theorem e_eq_inv {n:ℕ} {R:Type} [comm_ring R] (π: equiv.perm (fin n))  :  @e n R _ (π ) =  @e n R _ (π.symm ) := 
begin 
unfold e,
rw sig_eq_inv,

end 
theorem e_mul  {n:ℕ} {R:Type} [comm_ring R] (σ π :equiv.perm (fin n)) : @e n R _  (σ * π )= (@e n R _  σ ) *  @e n R _   π  := 
begin 
unfold e,
rw[← int.cast_mul, ← units.mul_coe, ← is_group_hom.mul equiv.perm.sign],
apply_instance,
end

theorem e_swap  {n:ℕ} {R:Type} [comm_ring R] {i j : fin n} (h : i ≠ j) : e (equiv.swap i j) = (-1 :R) := 
begin unfold e,
rw[equiv.perm.sign_swap],
simp,
exact h,
end