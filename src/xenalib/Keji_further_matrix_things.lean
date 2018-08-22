import init.function xenalib.Ellen_Arlt_matrix_rings algebra.module algebra.big_operators data.set.finite analysis.real data.complex.basic algebra.ring xenalib.Keji_permutations_for_matrices

open complex matrix

def Cross_out_column {R : Type} [ring R] {n : nat }
  (A : matrix R (n+1) (n+1)) (m : fin (n+1)) : matrix R n n := 
λ i j,
if j.1 < m.1 then  A (i.1 + 1) j.1 else 
  A (i.1 + 1) (j.1 + 1) 

def det_laplace {R : Type} [ring R]: Π {n: nat},  matrix R (n+1) (n+1) →  R
| 0 := λ A, A 0 0
| (n + 1) := λ A, 
  finset.sum finset.univ (λ k : fin (n+2), (-1 : R)^(k.1) * (A 0 k) *
 det_laplace (Cross_out_column A k))

noncomputable def det {n:ℕ} {R : Type} [comm_ring R] (A : matrix R n n) : R := 
finset.sum (finset.univ : finset (equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ  * (finset.prod (finset.univ : finset (fin n)) 
(λ (i:fin n), A (σ.1 i) i)))

def transpose {R : Type} [ring R] {n:ℕ} (A:matrix R n n) : matrix R n n :=
λ i j, A j i

postfix `ᵀ` : 100 := transpose

def Hermitian_conjugate  [ring ℂ ] {n:ℕ  } (A:matrix ℂ n n) : matrix ℂ n n:=
λ i j, conj (A j i)

postfix `†` : 100 := Hermitian_conjugate

def GL (n:ℕ) (R : Type) [ring R] := units (matrix R n n)

def Orthogornal (n : ℕ) : Type := {A : GL n ℝ // mul ℝ A.1 (A.1ᵀ) = identity_matrix ℝ ∧ mul ℝ (A.1ᵀ) A.1 = identity_matrix ℝ}

def Hermitian (n : ℕ) : Type := {A : matrix ℂ n n // mul ℂ A (A†) = (1 : matrix ℂ n n)}

theorem transpose_of_product (R : Type) [comm_ring R] {n : ℕ} (A B : matrix R n n) : (mul R A B)ᵀ  = mul R (Bᵀ ) (Aᵀ) := 
begin
  unfold mul,
  unfold transpose,
  simp[mul_comm]
end 

instance GL_group (n:ℕ) (R : Type) [ring R] : group (GL n R):=
begin
  unfold GL,
  apply_instance
end 

lemma matrix_prod_reorder_eq_prod {n : ℕ} {R : Type} [comm_ring R] (A : matrix R n n) (σ : equiv.perm (fin n)) (ρ : equiv.perm (fin n)) :
   (finset.prod (finset.univ : finset (fin n)) (λ (i : fin n), A (σ.1 ( ρ.1 i)) (ρ.1 i) )) =
    (finset.prod (finset.univ : finset (fin n)) (λ (i : fin n), A (σ.1 i) i)) := 
begin
  let t : Π a ∈ (@finset.univ (fin n) _ ), fin n := λ a ha, ρ.1 a, 
  rw[finset.prod_bij t],
  { simp },
  { intros,
    simp[t] },
  { intros,
    simp[t] at a,
    have H1 : function.injective ρ.1,
      { exact (equiv.bijective ρ).1 },
    apply H1,
    exact a },
  { intros,
    existsi (ρ.2 b),
    simp,
    simp[t],
    rw[ρ.4] }
end

lemma reorder_with_inv_old_order {n : ℕ} {R : Type} [comm_ring R] (A : matrix R n n) :
finset.sum (finset.univ : finset ( equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ *
(finset.prod (finset.univ : finset (fin n)) (λ (i : fin n), A (σ.1 (i)) i))) = 
finset.sum (finset.univ : finset ( equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)),e σ  *
(finset.prod (finset.univ : finset (fin n)) (λ (i:fin n), A i (σ.symm .1 i)))) :=
begin 
  congr,
  funext,
  conv { to_lhs, rw [← matrix_prod_reorder_eq_prod A σ (σ.symm)] },
  congr,
  funext,
  simp[equiv.symm],
  rw[σ .4]
end
lemma det_eq_trans {n : ℕ} {R : Type} [comm_ring R] (A : matrix R n n) : det A = det (Aᵀ) :=
begin 
  unfold det, 
  unfold transpose,
  rw[reorder_with_inv_old_order],
  have h : finset.sum (finset.univ : finset (equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ  *
  (finset.prod (finset.univ : finset (fin n)) (λ (i : fin n), A i (σ.symm .1 i)))) = finset.sum (finset.univ :
  finset ( equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ *
  (finset.prod (finset.univ : finset (fin n)) (λ (i : fin n), A i (σ.1 (i))))),
  { let t : Π a ∈ (@finset.univ ( equiv.perm (fin n)) _ ), equiv.perm (fin n) :=  λ a ha, a.symm, 
    rw[finset.sum_bij t],
    { intros,
      simp },
    { intros,
      simp[t],
      rw[e_eq_inv a] },
    { intros,
      simp[t] at a ,
      have H1 : function.left_inverse (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))) (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { unfold function.left_inverse,
        intros,
        show equiv.symm (x.symm) = x,
        simp },
      have H2 : function.right_inverse (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))) (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { unfold function.right_inverse,
        exact H1 },
      have H3: function.has_right_inverse (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { unfold function.has_right_inverse,
        existsi  (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
        exact H2 },
      have H41 : function.injective (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { exact function.injective_of_left_inverse H1 },
      have H42 : function.surjective (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { exact function.surjective_of_has_right_inverse H3 },
      have H4 : function.bijective (equiv.symm : (equiv.perm (fin n)) → (equiv.perm (fin n))),
      { unfold function.bijective,
        split,
        { exact H41 },
        { exact H42 } },
        exact H41 a },
      { intros,
        simp[t],
        existsi (equiv.symm b),
        simp } },
  rw[h]
end

local attribute [instance, priority 0] classical.prop_decidable

lemma col_swap_neg_col {n : ℕ} {R : Type} [comm_ring R] [decidable_eq R] (A : matrix R n n) (ρ : equiv.perm (fin n)) :
finset.sum (finset.univ : finset ( equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ * (finset.prod (finset.univ : finset (fin n)) 
(λ (i : fin n), A (σ.1 (i)) (ρ.1 (i))))) = e ρ * det A :=
begin 
  have H5:  (ρ.2 ∘ ρ.to_fun) = id,
  { funext, 
    simp,
    rw [ρ.3] },
  have H1 : finset.sum (finset.univ : finset ( equiv.perm (fin n))) (λ (σ : equiv.perm (fin n)), e σ * 
  (finset.prod (finset.univ : finset (fin n)) 
  (λ (i : fin n), A (σ.1 (i)) (ρ.1 i)))) = 
  finset.sum (finset.univ : finset ( equiv.perm (fin n))) (λ (μ : equiv.perm (fin n)),e (equiv.trans ρ μ ) * 
  (finset.prod (finset.univ: finset (fin n)) 
  (λ (i:fin n), A ((equiv.trans ρ  μ ).1 (i)) ( ρ.1 (i))))),
    unfold equiv.trans,
    simp,
    let t : Π a ∈ (@finset.univ ( equiv.perm (fin n)) _ ),  equiv.perm (fin n)  :=  λ a ha, equiv.trans ρ.symm a ,
    rw[finset.sum_bij t],
    { intros, 
      simp[t] },
    {  intros,
      simp[t],
      show _ =  e ( a * (ρ⁻¹ * ρ)) *
      finset.prod finset.univ (λ (x : fin n), A 
      (a.1 ((ρ.2 ∘ ρ.to_fun) x)) (ρ.to_fun x)),
      rw[H5],
      simp },
    { intros a₁ a₂,
      intros,
      simp[t] at a,
      rw [equiv.trans] at a,
      rw [equiv.trans] at a,
      have H2: a₁.to_fun ∘ (equiv.symm ρ).to_fun = a₂.to_fun ∘ (equiv.symm ρ).to_fun,
      { by  injection a },
      have H3 : (a₁.to_fun ∘ (equiv.symm ρ).to_fun) ∘ ρ.1 = (a₂.to_fun ∘ (equiv.symm ρ).to_fun) ∘ ρ.1,
      { rw[H2] },
      change  a₁.to_fun ∘ ρ.2 ∘ ρ.to_fun = a₂.to_fun ∘ ρ.2 ∘ ρ.to_fun at H3,
      rw[H5] at H3,
      simp at H3,
      exact equiv.eq_of_to_fun_eq H3 },
    { intros,
      simp[t],
      existsi equiv.trans ρ b,
      apply equiv.ext,
      simp },
    { change _ = finset.sum finset.univ
      (λ (μ : equiv.perm (fin n)),
      e (μ * ρ) *
      finset.prod finset.univ (λ (i : fin n), A ( μ.1 (ρ.1 i)) (ρ.to_fun i))) at H1,
      have H7 :  finset.sum finset.univ
       (λ (μ :  equiv.perm (fin n)),
         e (μ * ρ) *
           finset.prod finset.univ (λ (i : fin n), A (μ.to_fun (ρ.to_fun i)) (ρ.to_fun i)))= finset.sum finset.univ
      (λ (μ :  equiv.perm (fin n)),
         e (μ * ρ) *
           finset.prod finset.univ (λ (i : fin n), A (μ.to_fun i ) i)),
      { congr,
        funext,
        conv { to_rhs, rw [← matrix_prod_reorder_eq_prod A μ ρ ] } },
      rw[H1],
      rw[H7],
      conv in (e ( _ * ρ)) { rw [e_mul μ  ρ] },
      simp only [mul_comm ],
      simp only [_root_.mul_assoc],
      rw[← finset.mul_sum],
      rw[mul_comm (det A)  (e ρ)],
      refl }
end 

open finset

lemma disjoint_equiv_classes (α : Type*) [fintype α] [h : setoid α] [decidable_rel h.r] [decidable_eq α]:
∀ x ∈ @finset.univ (quotient h) _, ∀ y ∈ @finset.univ (quotient h) _, x ≠ y → 
    (finset.filter (λ b : α, ⟦b⟧ = x) finset.univ) ∩ (finset.filter (λ b : α, ⟦b⟧ = y) finset.univ) = ∅ :=
begin
  intros x hx y hx hxy,
  rw ←filter_and,
  rw ←filter_false,
  congr,funext,
    suffices : ⟦a⟧ = x ∧ ⟦a⟧ = y → false,
    simp [this],
  intro H,cases H with Hx Hy, rw Hx at Hy,apply hxy,exact Hy,
  intro x,show decidable false, refine is_false id
end

lemma sum_equiv_classes {α β : Type*} [add_comm_monoid α] [fintype β] (f : β → α)
  (h : setoid β) [decidable_rel h.r] [decidable_eq β] : 
finset.sum (@finset.univ β _) f = finset.sum finset.univ 
  (λ (x : quotient h), finset.sum (filter (λ b : β, ⟦b⟧ = x) finset.univ) f) := 
begin
  rw ←finset.sum_bind (disjoint_equiv_classes β),
  congr,symmetry,
  rw eq_univ_iff_forall,
  intro b,
  rw mem_bind,
  existsi ⟦b⟧,
  existsi (mem_univ ⟦b⟧),
  rw mem_filter,
  split,exact mem_univ b,refl
end

-- now let's define the equivalence relation on s by a is related to a and g(a) (and that's it)

definition gbar {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) :
(↑s : set β) → (↑s : set β) := 
--λ ⟨a,ha⟩,⟨g a ha,h₄ a ha⟩
λ x,⟨g x.val x.property, h₄ x.val x.property⟩

definition gbar_involution {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a) :
let gb := gbar g h₄ in
∀ x, gb (gb x) = x := 
begin
  intros gb x,
  apply subtype.eq,
  have H := h₅ x.val x.property,
  rw ←H,refl,
end 

private definition eqv {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a)
(a₁ a₂ : (↑s : set β)) : Prop :=
let gb := gbar g h₄ in a₁ = a₂ ∨ a₁ = gb a₂

private theorem eqv.refl {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a) :
∀ a : (↑s : set β), eqv g h₄ h₅ a a := λ a, or.inl rfl

private theorem eqv.symm {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a) :
∀ a₁ a₂ : (↑s : set β), eqv g h₄ h₅ a₁ a₂ → eqv g h₄ h₅ a₂ a₁
| a₁ a₂ (or.inl h) := or.inl h.symm
| a₁ a₂ (or.inr h) := or.inr (by rw h;exact (gbar_involution g h₄ h₅ a₂).symm)

private theorem eqv.trans {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a) :
∀ a₁ a₂ a₃ : (↑s : set β), eqv g h₄ h₅ a₁ a₂ → eqv g h₄ h₅ a₂ a₃ → eqv g h₄ h₅ a₁ a₃
| a₁ a₂ a₃ (or.inl h12) (or.inl h23) := or.inl (eq.trans h12 h23)
| a₁ a₂ a₃ (or.inl h12) (or.inr h23) := or.inr (h12.symm ▸ h23)
| a₁ a₂ a₃ (or.inr h12) (or.inl h23) := or.inr (h23 ▸ h12)
| a₁ a₂ a₃ (or.inr h12) (or.inr h23) := or.inl (by rw [h12,h23];exact (gbar_involution g h₄ h₅ a₃))

private theorem is_equivalence {β : Type*} {s : finset β} (g : Π a ∈ s, β) 
(h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a)
: equivalence (eqv g h₄ h₅) := ⟨eqv.refl g h₄ h₅,eqv.symm g h₄ h₅,eqv.trans g h₄ h₅⟩

instance {β : Type*} [decidable_eq β] {s : finset β} (g : Π a ∈ s, β) 
  (h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a) : decidable_rel (eqv g h₄ h₅) :=
begin
  intros a₁ a₂,
  by_cases H12 : a₁ = a₂,
    refine is_true (or.inl H12),
  by_cases H12g : a₁ = gbar g h₄ a₂,
    refine is_true (or.inr H12g),
  refine is_false _,
  intro H,cases H,
    apply H12,exact H,
    apply H12g,exact H,
end

lemma sum_zero_of_pair_mem_sum_zero {α β : Type*} [add_comm_monoid α] [decidable_eq β] {f : β → α}
  {s : finset β} (g : Π a ∈ s, β) (h₀ : ∀ a ha, f a + f (g a ha) = 0)
  (h₁ : ∀ a ha, g a ha ≠ a) (h₂ : ∀ a₁ a₂ ha₁ ha₂, g a₁ ha₁ = g a₂ ha₂ → a₁ = a₂)
  (h₃ : ∀ a ∈ s, ∃ b hb, g b hb = a) (h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a ) :
   s.sum f = 0 := 
begin
  let gb := gbar g h₄,
  let β' := ↥(↑s : set β),
  letI fβ' : fintype β' := by apply_instance,
  let inst_2 : fintype β' := by apply_instance,
  let f' : β' → α := λ b,f b,
  let h : setoid β' := {r := eqv g h₄ h₅,iseqv := is_equivalence g h₄ h₅},
  let inst_4 : decidable_eq β' := by apply_instance,
  let inst_3 : decidable_rel h.r := by apply_instance,
  have H : s.sum f = sum univ f',
  { let g' : β' → β := λ x, x.val,
    let s' : finset β' := finset.univ,
    have Hinj : ∀ x ∈ s', ∀ y ∈ s', g' x = g' y → x = y,
    { intros x Hx y Hy,exact subtype.eq,
    },
    have H2 := @sum_image β α β' f _ _ _ s' g' Hinj,
    have H3 : image g' s' = s,
    { ext,split,
      { rw finset.mem_image,
        intro Ha,
        cases Ha with b Hb,
        cases Hb with Hb Hg',
        rw ←Hg',
        exact b.property,
      },
      intro Ha,
      rw finset.mem_image,
      existsi (⟨a,Ha⟩ : β'),
      existsi (mem_univ _),refl
    },
    rw ←H3,
    rw H2,
    refl
  },
  rw H,
  -- now finally rewrite sum_equiv_classes
  rw @sum_equiv_classes α β' _ fβ' f' h _ _,
  rw ←sum_const_zero,
  congr,funext,
  let b := quotient.out x,
  suffices : (filter (λ (b : β'), ⟦b⟧ = x) univ) = insert b (finset.singleton (gb b)),
  { rw this,
    have H2 : b ∉ finset.singleton (gb b),
      rw mem_singleton,
      intro H3,replace H3 := H3.symm,
      apply h₁ b.val b.property,
      have H4 : (gb b).val = b.val := by rw H3,
      exact H4,
    rw finset.sum_insert H2,
    rw finset.sum_singleton,
    show f b.val + f (g b.val b.property) = 0,
    exact h₀ b.val b.property
  },
  clear H,
  have H : ∀ c : β', ⟦c⟧ = x ↔ c = b ∨ c = gb b,
  { intro c,split,swap,
      intro H2,cases H2,rw H2,simp,
      rw H2,
      suffices : ⟦gb b⟧ = ⟦b⟧, by simp [this],
      rw quotient.eq,
      exact or.inr rfl,
    have H : x = ⟦b⟧ := by simp,
    rw H,rw quotient.eq,
    intro H2, cases H2,left,exact H2,
    right,exact H2,
  },
  ext,
  have H2 : a ∈ insert b (finset.singleton (gb b)) ↔ a = b ∨ a = gb b := by simp,
    rw H2,
    rw ←H a,
    simp,
end
theorem det_eq_zero_of_col_eq {n:ℕ} {R : Type} [comm_ring R] (A: matrix R n n) : (∃ (i j: fin n ),(i ≠ j) ∧  ∀ (x: fin n), A x i = A x j) → det A = 0 :=
  begin 
  intros,
  unfold det,
  cases a with i,
  cases a_h with j,
  let g : Π a ∈ (finset.univ: finset( equiv.perm (fin n))),  equiv.perm (fin n) := λ σ  hσ , σ *  (equiv.swap i j),
  rw[sum_zero_of_pair_mem_sum_zero g],
  { intros,
    simp[g] ,
    show e (a) * finset.prod finset.univ (λ (i : fin n), A (a.to_fun i) i) +
    e (a * (equiv.swap i j)) * finset.prod finset.univ (λ (x : fin n), A ((a * equiv.swap i j).to_fun x) x) =
    0,
    rw[e_mul a (equiv.swap i j)],
    have h1 : i ≠ j,
    exact absurd h a_h_h.1, 
    rw[e_swap h1],
     rw[mul_comm  (e (a)) (-1 : R) ],
        rw[neg_one_mul],
        rw[add_eq_zero_iff_eq_neg],   
        simp,
        rw[eq_comm],
        let t : Π a ∈ (finset.univ: finset( fin n)), fin n:=  
        λ a ha, (equiv.swap i j) a,
        rw[finset.prod_bij t],
        { intros,
          simp },
        { intros,
          simp[t],
          by_cases h1 : a_1 =i,
        { rw[h1],
          show A (a ((equiv.swap i j)i)) i = A (a ((equiv.swap i j)i)) ((equiv.swap i j) i),
          rw[equiv.swap_apply_left],
          show A (a.1 j) i = A (a.1 j) j,
          exact a_h_h.2 (a.1 j) },
        by_cases h2 : a_1 =j,
        { rw[h2],
          show A (a ((equiv.swap i j)j)) j = A (a ((equiv.swap i j)j)) ((equiv.swap i j) j),
          rw[equiv.swap_apply_right],
          show A (a.1 i) j = A (a.1 i) i,
          rw[ ← a_h_h.2 (a.1 i)] },
        show A (a ((equiv.swap i j)a_1)) a_1 = A (a ((equiv.swap i j)a_1)) ((equiv.swap i j) a_1),
        rw[equiv.swap_apply_of_ne_of_ne],
        exact h1,
        exact h2 },
        simp[t],
        intros,
        have H2: function.injective (equiv.swap i j).1,
        { exact (equiv.bijective (equiv.swap i j) ).1 },
        existsi ((equiv.swap i j).2 b),
        simp,
        simp[t],
        show _ = (equiv.swap i j).1 ((equiv.swap i j).inv_fun b),
        rw[(equiv.swap i j).4],
      
  { intros,
    simp[g],
    assume h,
    rw[← _root_.mul_one (a:  equiv.perm (fin n))] at h,
    rw[_root_.mul_assoc] at h,
    rw[ mul_left_inj a] at h,
    simp at h,
    have H3: (equiv.swap i j) i = (1 :  equiv.perm (fin n)) i,
    { rw[h] },
    have H4:(equiv.swap i j) i = j,
    { rw[equiv.swap_apply_left] },
    replace H3: (equiv.swap i j).1 i = (1 :  equiv.perm (fin n)).1 i := H3,
    replace H4: (equiv.swap i j).1 i = j := H4,
    rw[eq_comm] at H4,
    have H6: (1 :  equiv.perm (fin n)).to_fun i = j,
    { rw[eq.trans H4 H3] },
    exact a_h_h.1 H6 },
  { intros,
    simp[g] at a,
    exact a },
  { intros,
    simp[g],
    existsi (a * (equiv.swap i j)⁻¹),
    rw[_root_.mul_assoc],
    rw[mul_left_inv],
    simp },
  { intros,
    simp[g],
    rw[_root_.mul_assoc],
    have H7: equiv.swap i j * (equiv.swap i j)⁻¹ = (1:  equiv.perm (fin n)),
    { rw[mul_right_inv] },
    have H8 : (equiv.swap i j)⁻¹ = equiv.swap i j ,
    { refl },
    rw[H8] at H7,
    rw[H7],
    simp },
  { intros,
    simp } },
end

theorem not_bij_not_inj {α : Type* } [s : fintype α ] {f : α  → α} (h: ¬function.bijective f ) : ¬function.injective f:= 
begin
intro,
apply h,
exact ⟨a, fintype.injective_iff_surjective.1 a⟩,
end

theorem det_mul {n:ℕ} {R : Type} [comm_ring R] (A: matrix R n n) (B: matrix R n n) : 
det(mul R A B) = det A * det B:=
begin 
unfold det,
unfold mul,
let t := (λ (a : fin n), (finset.univ: finset (fin n))),
simp only [@finset.prod_sum],
conv {to_lhs, congr,skip,funext,rw finset.mul_sum},
rw[finset.sum_comm],
simp only[finset.prod_mul_distrib],
simp only [mul_comm],
simp only [mul_comm (e ( _ )) _ ],
simp only [_root_.mul_assoc _ _ (e( _ ))],
conv {to_lhs, congr,skip,funext,rw ← finset.mul_sum},
simp only [mul_comm ( _ )  (e ( _ ))  ],
have H1: finset.sum (finset.pi finset.univ (λ (a : fin n), finset.univ))
      (λ (y : Π (a : fin n), a ∈ finset.univ → fin n),
         finset.prod (finset.attach finset.univ) (λ (x : {x // x ∈ finset.univ}), B (y (x.val) _) (x.val)) *
           finset.sum finset.univ
             (λ (x :  equiv.perm (fin n)),
                e (x) *
                  finset.prod (finset.attach finset.univ)
                    (λ (x_1 : {x // x ∈ finset.univ}), A (x.to_fun (x_1.val)) (y (x_1.val) _)))) = 
                     finset.sum (finset.univ : finset (fin n → fin n))
      (λ (y : fin n → fin n),
         finset.prod (finset.univ : finset( fin n) ) (λ (x : fin n), B (y x) x) *
           finset.sum finset.univ
             (λ (x :  equiv.perm (fin n)),
                e (x) *
                  finset.prod (finset.univ : finset( fin n) ) 
                    (λ (x_1 : fin n), A (x.to_fun x_1) (y x_1 )))),

let t' : Π a ∈ (finset.pi (finset.univ :finset(fin n)) (λ (a : fin n), (finset.univ :finset(fin n)))), (fin n → fin n)  := 
 λ a ha, (λ (x: fin n), a x (finset.mem_univ x) ),
rw[finset.sum_bij t'],
intros,
simp,
intros,
let t'' : Π a ∈ (finset.attach (finset.univ : finset (fin n))), fin n:= 
λ a ha, a.val,
have H12 : finset.prod (finset.attach (finset.univ : finset (fin n))) 
(λ x , B (a x.val (finset.mem_univ _)) (x.val)) =
finset.prod (finset.univ : finset (fin n)) 
(λ x , B (a x (finset.mem_univ _)) x),
rw[finset.prod_bij t''],
intros, 
simp,
intros,
simp,
intros,
simp[t''] at a_1,
rw[subtype.eq a_1],
intros,
existsi ( ⟨ b, (finset.mem_univ _) ⟩ :  {x // x ∈ finset.univ}) ,
refine exists.intro (by simp) _,
refl,
rw[H12],
have H13: finset.sum finset.univ (λ (x :  equiv.perm (fin n)),
           e (x) *
             finset.prod (finset.attach finset.univ)
               (λ (x_1 : {x // x ∈ finset.univ}), A (x.to_fun (x_1.val))
                (a (x_1.val) (finset.mem_univ _))))= finset.sum finset.univ (λ (x :  equiv.perm (fin n)),
           e (x) *
             finset.prod ( finset.univ)
               (λ x_1 , A (x.to_fun x_1)
                (a x_1 (finset.mem_univ _)))),
congr,
funext,
rw [finset.prod_bij t''],
intros, 
simp,
intros,
simp,
intros,
simp[t''] at a_1,
rw[subtype.eq a_1],
intros,
existsi ( ⟨ b, (finset.mem_univ _) ⟩ :  {x // x ∈ finset.univ}) ,
refine exists.intro (by simp) _,
refl,
rw[H13],
intros,
simp[t'] at a,
funext,
have := congr_fun a x, exact this,
intros,
refine exists.intro (λ(x: fin n) (h ), b x) _,
simp,
rw[H1],
have H2: (finset.univ : finset (fin n → fin n)) = 
(finset.filter (λ f, function.bijective f) (finset.univ : finset (fin n → fin n))) ∪
 (finset.filter (λ f : fin n -> fin n, ¬ function.bijective f ) 
 (finset.univ : finset (fin n → fin n))),
ext,
simp [classical.em],
rw[H2],
rw[finset.sum_union],
swap 2,
ext,simp,
have H21: finset.sum (finset.filter (λ (f : fin n → fin n), function.bijective f) 
   finset.univ)
        (λ (y : fin n → fin n),
           finset.prod finset.univ (λ (x : fin n), B (y x) x) *
             finset.sum finset.univ
               (λ (x :  equiv.perm (fin n)), e (x) * finset.prod finset.univ (λ (x_1 : fin n),
                A (x.to_fun x_1) (y x_1)))) = 
        finset.sum (finset.univ : finset ( equiv.perm (fin n)))
        (λ y,
           finset.prod finset.univ (λ (x : fin n), B (y.1 x) x) *
             finset.sum finset.univ
               (λ (x :  equiv.perm (fin n)), e (x) * finset.prod finset.univ (λ (x_1 : fin n),
                A (x.to_fun x_1) (y.1 x_1)))),

let t : Π a ∈ (finset.univ : finset ( equiv.perm (fin n))), fin n → fin n  :=
  λ a ha, a.1,
rw[finset.sum_bij t],
intros,
simp,
simp[t],
exact a.bijective,
intros,
simp,
intros,
simp[t] at a,
exact equiv.eq_of_to_fun_eq a,
intros,
simp[t],
have H22: function.bijective b,
   {exact (finset.mem_filter.1 H).2},
existsi @equiv.of_bijective _ _ b H22,
exact eq.symm (equiv.of_bijective_to_fun H22),
rw[H21],
simp only[col_swap_neg_col],
simp only[mul_comm],
simp only[_root_.mul_assoc],
rw[← finset.mul_sum],
rw[← det],
have H3: finset.sum (finset.filter (λ (f : fin n → fin n), ¬function.bijective f) finset.univ)
        (λ (y : fin n → fin n),
           finset.prod finset.univ (λ (x : fin n), B (y x) x) *
             finset.sum finset.univ
               (λ (x :  equiv.perm (fin n)), e (x) * 
               finset.prod finset.univ (λ (x_1 : fin n), A (x.to_fun x_1) (y x_1)))) = 0,
conv
begin 
to_rhs,
rw[← @finset.sum_const_zero _ _ (finset.filter (λ (f : fin n → fin n), ¬function.bijective f) finset.univ) _],
end,
refine finset.sum_congr rfl _,
intros,
have H4: finset.sum finset.univ
        (λ (x_1 :  equiv.perm (fin n)),
           e (x_1) * finset.prod finset.univ (λ (x_1_1 : fin n), A (x_1.to_fun x_1_1) (x x_1_1))) =
    0,
    have h1: ¬ function.injective x,
    exact @not_bij_not_inj (fin n) _ x (finset.mem_filter.1 H).2,
    unfold function.injective at h1,
     rw[classical.not_forall] at h1,
    simp only[classical.not_forall] at h1,
    cases h1 with i,
    cases h1_h with j,
    cases h1_h_h with h,
    let W: matrix R n n:= λ i j, A i (x j),
    show finset.sum finset.univ
      (λ (x_1 :  equiv.perm (fin n)), e (x_1) * finset.prod finset.univ (λ (x_1_1 : fin n), W (x_1.to_fun x_1_1)  x_1_1)) =
    0,
    rw[← det],
    rw[det_eq_zero_of_col_eq],
    existsi i,
    existsi  j,
    split,
    exact h1_h_h_h,
    intro,
   simp[W],
   rw[h],
   rw[H4],
   simp,
   rw[H3],
  simp,
  refl,
end










