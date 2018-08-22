import xenalib.Group_actions data.fintype data.set.finite data.equiv.basic xenalib.Ellen_Arlt_matrix_rings algebra.big_operators data.set.finite group_theory.coset algebra.group
import group_theory.perm
local attribute [instance] classical.prop_decidable









open fintype 
set_option pp.proofs true
-- noncomputable instance {n : ℕ} : fintype {f : fin n→ fin n // function.bijective f}  := 
-- set_fintype _
def S (n: ℕ ) := equiv.perm (fin n)
instance (n : ℕ) : has_coe_to_fun (S n) := by unfold S; apply_instance
-- def e {n:ℕ} {R:Type} [comm_ring R] (σ : fin n → fin n) : R:= sorry 
-- theorem Sig_eq_inv {n:ℕ} {R:Type} [comm_ring R] (π: S n)  : @e n R _  π.1 = e (π.symm).1 := sorry
-- theorem sig_mul  {n:ℕ} {R:Type} [comm_ring R] (σ π : fin n → fin n) : @e n R _  (σ ∘ π  )= (@e n R _  σ ) *  @e n R _   π  := sorry
-- theorem sig_swap  {n:ℕ} {R:Type} [comm_ring R] (i j : fin n): e (equiv.swap i j).1 = (-1 :R) := sorry
-- noncomputable instance Sn_finite {n:ℕ}: fintype (S n):=
-- fintype.of_surjective 
-- (λ (f : {f : fin n → fin n // function.bijective f}), equiv.of_bijective f.2) 
-- begin 
-- unfold function.surjective,
-- simp,
-- intro b,
-- let f:{f : fin n → fin n // function.bijective f}:=  ⟨ b.1,b.bijective⟩,
-- existsi f.1,
-- existsi  f.2,
-- apply equiv.ext,
-- intro x,
-- rw equiv.of_bijective_to_fun,
-- refl,
-- end
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
variables (n :ℕ) (σ : S n)


open function
def compose: ℕ → (fin n → fin n) → (fin n → fin n)
| 0 σ := σ  
| (i + 1) σ  := comp σ (compose i σ )
def cyclic_subtype :Type :=  {x : S n // ∃ (j: ℕ), (compose j σ.1) = x.1}

def Cyclic_Group_generated_by (σ : S n ): group {x : S n // ∃ (j: ℕ), (compose j σ.1) = x.1} :=



def Cycle (σ : S n): Prop:= ∃! (i:fin n), card (is_group_action.orbit equiv.to_fun i) > 1,






def f' {n:ℕ }(f:is_group_action.stabilizer (equiv.to_fun: S (n+1) → 
  fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩): fin n → fin n := 
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
@[simp] lemma fin_thing {n : ℕ} (a : fin n) : (⟨a.1, a.2⟩ : fin n) = a := by cases a;refl 
#print is_group_action.mul
theorem f'_bijective {n:ℕ }(f:is_group_action.stabilizer (equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩): function.bijective(f' f):=
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
existsi  (⟨  (f.val⁻¹ .to_fun (fin.raise b)).val,
begin 
have H1: f.val⁻¹ ∈  stabilizer 
(equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩,
rw[is_subgroup.inv_mem_iff],
exact f.2,
 have : ((f.val⁻¹).to_fun ⟨n, nat.lt_succ_self n⟩).val = n := 
 fin.veq_of_eq H1,
 refine lt_of_le_of_ne _ _,
  exact (nat.le_of_lt_succ (f.1.2 (fin.raise b)).2),
  assume h,
  conv at h {to_rhs, rw ← this},
  have h : b.val = n := fin.veq_of_eq ((f.val⁻¹).bijective.1 (fin.eq_of_veq h)),
  have : b.val < n := b.2,
  simpa[lt_irrefl, h] using this,
  
end⟩ : fin n),
simp [fin.raise],
apply fin.eq_of_veq,
simp,
-- (is_group_action.mul (equiv.to_fun : S (n+1) → fin (n+1) → fin (n+1)) _ _ _).symm._,
-- rw mul_inv_self,
-- exact b.2,
rw ← is_group_action.mul (equiv.to_fun : S (n+1) → fin (n+1) → fin (n+1)),
rw mul_inv_self,
refl,
end 
open function 
noncomputable def F : is_group_action.stabilizer (equiv.to_fun: S (n+1) → fin (n+1) → fin (n+1)) ⟨n, nat.lt_succ_self _⟩ → S n:=
λ f, ⟨ (f' f),surj_inv (f'_bijective f).2 , left_inverse_surj_inv (f'_bijective f), right_inverse_surj_inv(f'_bijective f).2⟩  

theorem bijection_form_stab_to_Sn: bijective (F n):=
begin 
unfold function.bijective,
split,
unfold injective,
intros,
simp[F] at a,
refine subtype.eq (equiv.ext _ _ _),
have : f' a₁ = f' a₂, by injection a,
simp [f'] at this,

have:= congr_fun this,
dsimp at this,
intro a,
by_cases a.1 < n,
have := (fin.veq_of_eq (this_1 ⟨a.1, h⟩)),
simp [fin.raise] at this,
exact fin.eq_of_veq this,
have H1 : n≤ a.1,
exact le_of_not_lt h,
have H2: a.1 ≤ n,
exact nat.le_of_lt_succ a.2,
have H3: a.1= n,
exact le_antisymm H2 H1,
have H4: a= ⟨n, nat.lt_succ_self _⟩,
exact fin.eq_of_veq H3,
rw[H4],
have H5: (a₁.val) ⟨n, _⟩ =⟨n, _⟩,
exact a₁.2,
have H6: (a₂.val) ⟨n, _⟩ =⟨n, _⟩,
exact a₂.2,
exact eq.trans H5 H6.symm,
unfold surjective,
intro,
simp[F],
let k:= λ(x:fin(n+1)),if hxn : x.1<n then (⟨b.1 ⟨x.1, hxn⟩,
begin
have H1: (b.1 ⟨x.1, hxn⟩).1 < n,
  exact (b.1 ⟨x.1, hxn⟩).2,
  exact lt_trans H1 (nat.lt_succ_self n),
 end ⟩ : fin(n+1)) else n,
existsi( ⟨k ,λ(x:fin(n+1)),if hxn : x.1<n then ⟨b.2 ⟨x.1, hxn⟩,
begin
have H1: (b.2 ⟨x.1, hxn⟩).1 < n,
  exact (b.2 ⟨x.1, hxn⟩).2,
  exact lt_trans H1 (nat.lt_succ_self n),
 end ⟩ else n,
 begin 
 unfold left_inverse,
 intro,
 by_cases x.val < n,
 simp [h, dif_pos h],
--have H1: 
            

 

 end, sorry⟩ :fin (n + 1) ≃ fin (n + 1))
end
#check eq.trans
#check le_antisymm
#check le_of_not_lt
theorem mag_S {n:ℕ}: fintype.card (S n) = nat.fact n := sorry
#check nat.le_of_lt_succ
#check nat.add_one
#check lt_trans