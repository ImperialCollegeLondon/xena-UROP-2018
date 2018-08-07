import init.function xenalib.Ellen_Arlt_matrix_rings algebra.module algebra.big_operators data.set.finite analysis.real data.complex.basic algebra.ring xenalib.Keji_permutation_group

open complex matrix

def Cross_out_column {R : Type} [ring R] {n : nat }
  (A:matrix R (n+1) (n+1)) (m :fin (n+1)): matrix R n n := 
λ i j,
if j.1 < m.1 then  A (i.1+1) j.1 else 
  A (i.1+1) (j.1+1) 
def det_laplace {R : Type} [ring R]: Π {n: nat},  matrix R (n+1) (n+1) →  R
| 0 := λ A, A 0 0
| (n + 1) := λ A, 
  finset.sum finset.univ (λ k : fin (n+2), (-1: R)^(k.1) *(A 0 k) *
 det_laplace (Cross_out_column A k))

noncomputable def det {n:ℕ} {R : Type} [comm_ring R] (A: matrix R n n): R:= 
finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) * (finset.prod (finset.univ: finset (fin n)) 
(λ (i:fin n), A (σ.1 (i)) i)))


def transpose {R : Type} [ring R] {n:ℕ  }(A:matrix R n n):  matrix R n n:=
λ i j, A j i
postfix `ᵀ`:100 := transpose
def Hermitian_conjugate  [ring ℂ ] {n:ℕ  }(A:matrix ℂ n n):  matrix ℂ n n:=
λ i j, conj (A j i)
postfix `†`:100 := Hermitian_conjugate
def GL (n:ℕ) ( R : Type) [ring R]:= units (matrix R n n)
def Orthogornal ( n: ℕ): Type:= {A :GL n ℝ   // mul ℝ  A.1 ( A.1ᵀ)= identity_matrix ℝ  ∧ mul ℝ (A.1ᵀ) A.1 = identity_matrix ℝ  }
def Hermitian ( n: ℕ) : Type:= {A :matrix ℂ n n //  mul ℂ A (A†)= (1 : matrix ℂ n n)}
theorem transpose_of_product ( R : Type) [comm_ring R] {n:ℕ}(A B:matrix R n n): (mul R A B)ᵀ  = mul R (Bᵀ ) (Aᵀ) := 
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

lemma L1 {n:ℕ } {R : Type} [comm_ring R] (A: matrix R n n) (σ : S n) (ρ : S n) :
   (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A (σ.1 ( ρ.1 (i))) (ρ.1 (i)) )) =
    (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A (σ.1 (i)) i)):= 
begin
let t :Π a ∈ (@finset.univ (fin n) _ ), fin n  :=  λ a ha, ρ.1 a, 
rw[finset.prod_bij t],
simp,
intros,
simp[t],
intros,
simp[t] at a,
have H1: function.injective ρ.1,
exact (equiv.bijective ρ ).1,
apply H1,
exact a,
intros,
existsi (ρ.2 b),
simp,
simp[t],
rw[ρ.4],
end
#check equiv
lemma L2 {n: ℕ } {R : Type} [comm_ring R] (A: matrix R n n) :
finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) *
 (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A (σ.1 (i)) i))) = 
 finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) *
 (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A i (σ.symm .1 i)))):=
 begin 
congr,
funext,
conv
  begin
    to_lhs,
    rw [← L1 A σ (σ.symm)],
  end,
 congr,
 funext,
 simp[equiv.symm],
 rw[σ .4],
 end

 lemma L3 {n:ℕ} {R : Type} [comm_ring R] (A: matrix R n n) : finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) *
 (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A i (σ.symm .1 i)))) = finset.sum (finset.univ :
  finset (S n)) (λ (σ:S n),e(σ.1) *
 (finset.prod (finset.univ: finset (fin n)) (λ (i:fin n), A i (σ.1 (i))))) :=
 begin 
 let t :Π a ∈ (@finset.univ (S n) _ ), S n  :=  λ a ha, a.symm, 
 rw[finset.sum_bij t],
 intros,
 simp,
 intros,
 simp[t],
 congr,
 intros,
 simp[t] at a,
 have H1 : function.left_inverse (equiv.symm: (S n) → (S n)) (equiv.symm: (S n) → (S n)) ,
unfold function.left_inverse,
intros,
 show equiv.symm ( x.symm) = x,
 simp,
  have H2 : function.right_inverse (equiv.symm: (S n) → (S n)) (equiv.symm: (S n) → (S n)) ,
 unfold function.right_inverse,
 exact H1,
 have H3: function.has_right_inverse  (equiv.symm: (S n) → (S n)),
 unfold function.has_right_inverse,
 existsi  (equiv.symm: (S n) → (S n)),
 exact H2,
 have H41: function.injective (equiv.symm: (S n) → (S n)),
exact function.injective_of_left_inverse H1 ,
have H42: function.surjective (equiv.symm: (S n) → (S n)),
exact function.surjective_of_has_right_inverse H3,
 have H4 : function.bijective (equiv.symm: (S n) → (S n)) ,
 unfold function.bijective,
 split,
 exact H41,
 exact H42,
 exact H41 a,
 intros,
 simp[t],
 existsi (equiv.symm b),
 simp,
end
theorem det_eq_trans {n:ℕ } {R : Type} [comm_ring R] (A: matrix R n n) : det A = 
det (Aᵀ):=
begin 
unfold det, 
unfold transpose,
rw[L2],
rw[L3],
end 
local attribute [instance] classical.prop_decidable
lemma M1 {n:ℕ} {R : Type} [comm_ring R] [decidable_eq R] (A: matrix R n n) (ρ : S n):
finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) * (finset.prod (finset.univ: finset (fin n)) 
(λ (i:fin n), A (σ.1 (i)) ( ρ.1 (i))))) = e (ρ.1) * det A :=
begin 
have H5:  (ρ.2 ∘ ρ.to_fun) = id,
funext, 
simp,
rw [ρ.3],
have H1: finset.sum (finset.univ : finset (S n)) (λ (σ :S n),e(σ.1 ) * 
(finset.prod (finset.univ: finset (fin n)) 
(λ (i:fin n), A (σ.1 (i)) ( ρ.1 (i))))) = 
finset.sum (finset.univ : finset (S n)) (λ (μ  :S n),e (equiv.trans ρ μ ).1 * 
(finset.prod (finset.univ: finset (fin n)) 
(λ (i:fin n), A ((equiv.trans ρ  μ ).1 (i)) ( ρ.1 (i))))),
unfold equiv.trans,
simp,
let t : Π a ∈ (@finset.univ (S n) _ ), S n  :=  λ a ha, equiv.trans ρ.symm a ,
rw[finset.sum_bij t],
intros, 
simp[t],
intros,
simp[t],
show _ =  e ( a.1 ∘ (ρ.2  ∘ ρ.to_fun)) *
      finset.prod finset.univ (λ (x : fin n), A 
      ((equiv.trans (equiv.symm ρ) a).to_fun (ρ.to_fun x)) (ρ.to_fun x)),


rw[H5],
simp,

show _ =  e (a.to_fun) *
      finset.prod finset.univ (λ (x : fin n), A 
      ( (a.1 ∘ ρ.2 ∘ ρ.to_fun) x ) (ρ.to_fun x)),
rw[H5],
simp,
simp[t],
intros a₁ a₂,
intro,

rw [equiv.trans] at a,
rw [equiv.trans] at a,
have H2: a₁.to_fun ∘ (equiv.symm ρ).to_fun = a₂.to_fun ∘ (equiv.symm ρ).to_fun,
by injection a,
have H3:  (a₁.to_fun ∘ (equiv.symm ρ).to_fun) ∘ ρ.1 = (a₂.to_fun ∘ (equiv.symm ρ).to_fun) ∘ ρ.1,
rw[H2],
change  a₁.to_fun ∘ ρ.2 ∘ ρ.to_fun = a₂.to_fun ∘ ρ.2 ∘ ρ.to_fun at H3,
rw[H5] at H3,
simp at H3,
exact equiv.eq_of_to_fun_eq H3,
intros,
simp[t],
existsi equiv.trans ρ b,
apply equiv.ext,
simp,
change _ = finset.sum finset.univ
      (λ (μ : S n),
         e ( μ.1 ∘ ρ.1 ) *
           finset.prod finset.univ (λ (i : fin n), A ( μ.1 (ρ.1 i)) (ρ.to_fun i))) at H1,
have H7:  finset.sum finset.univ
      (λ (μ : S n),
         e (μ.to_fun ∘ ρ.to_fun) *
           finset.prod finset.univ (λ (i : fin n), A (μ.to_fun (ρ.to_fun i)) (ρ.to_fun i)))= finset.sum finset.univ
      (λ (μ : S n),
         e (μ.to_fun ∘ ρ.to_fun) *
           finset.prod finset.univ (λ (i : fin n), A (μ.to_fun i ) i)),
congr,
funext,
conv
  begin
    to_rhs,
    rw [← L1 A μ ρ ],
  end,
rw[H1],
rw[H7],

conv in (e ( _ ∘ ρ.to_fun))
begin
rw [sig_mul μ.to_fun  ρ.to_fun],
end,
show finset.sum finset.univ
      (λ (μ : S n),e (ρ.to_fun) * e (μ.to_fun)  * 
      finset.prod finset.univ (λ (i : fin n), A (μ.to_fun i) i)) =_,
simp only [_root_.mul_assoc],
rw[← finset.mul_sum],
refl,
end 

#check finset.strong_induction_on 
lemma sum_keji {α β : Type*} [add_comm_monoid α] {f : β → α}
  {s : finset β} (g : Π a ∈ s, β) (h₁ : ∀ a ha, f a + f (g a ha) = 0)
  (h₂ : ∀ a ha, g a ha ≠ a) (h₂ : ∀ a₁ a₂ ha₁ ha₂, g a₁ ha₁ = g a₂ ha₂ → a₁ = a₂)
  (h₃ : ∀ a ∈ s, ∃ b hb, g b hb = a) (h₄ : ∀ a ha, g a ha ∈ s) (h₅ : ∀ a ha, g (g a ha) (h₄ a ha) = a ) : s.sum f = 0 := sorry

instance (n:ℕ) :(group (S n)) := 
begin 
unfold S,
apply_instance,
end
theorem M2 {n:ℕ} {R : Type} [comm_ring R] (A: matrix R n n) : (∃ (i j: fin n ),(i ≠ j) ∧  ∀ (x: fin n), A x i = A x j) → det A = 0 :=
begin 
intros,
unfold det,
cases a with i,
cases a_h with j,
let g : Π a ∈ (finset.univ: finset(S n)), S n := λ σ  hσ , σ *  (equiv.swap i j),
rw[sum_keji g],
intros,
simp[g],
show e (a.to_fun) * finset.prod finset.univ (λ (i : fin n), A (a.to_fun i) i) +
      e (a.1 ∘ (equiv.swap i j).1) * finset.prod finset.univ (λ (x : fin n), A ((a * equiv.swap i j).to_fun x) x) =
    0,
rw[sig_mul a.to_fun (equiv.swap i j).to_fun],
rw[sig_swap],
rw[mul_comm  (e (a.to_fun)) (-1 : R) ],
rw[neg_one_mul],
rw[add_eq_zero_iff_eq_neg],   
simp,
rw[eq_comm],
let t : Π a ∈ (finset.univ: finset( fin n)), fin n:=  
λ a ha, (equiv.swap i j).1 a,
rw[finset.prod_bij t],
intros,
simp,
intros,
simp[t],
by_cases h1 : a_1 =i,
rw[h1],
show A (a ((equiv.swap i j)i)) i = A (a ((equiv.swap i j)i)) ((equiv.swap i j) i),
rw[equiv.swap_apply_left],
show A (a.1 j) i = A (a.1 j) j,
exact a_h_h.2 (a.1 j),
by_cases h2 : a_1 =j,
rw[h2],
show A (a ((equiv.swap i j)j)) j = A (a ((equiv.swap i j)j)) ((equiv.swap i j) j),
rw[equiv.swap_apply_right],
show A (a.1 i) j = A (a.1 i) i,
rw[ ← a_h_h.2 (a.1 i)],
 show A (a ((equiv.swap i j)a_1)) a_1 = A (a ((equiv.swap i j)a_1)) ((equiv.swap i j) a_1),
rw[equiv.swap_apply_of_ne_of_ne],
exact h1,
exact h2,
simp[t],
intros,
have H2: function.injective (equiv.swap i j).1,
exact (equiv.bijective (equiv.swap i j) ).1,
apply H2,
exact a_1,
intros,
existsi ((equiv.swap i j).2 b),
simp,
simp[t],
rw[(equiv.swap i j).4],
intros,
simp[g],
assume h,
rw[← _root_.mul_one (a: S n)] at h,
rw[_root_.mul_assoc] at h,
rw[ mul_left_inj a] at h,
simp at h,
have H3: (equiv.swap i j) i = (1 : S n) i,
rw[h],
have H4:(equiv.swap i j) i = j,
rw[equiv.swap_apply_left],
replace H3: (equiv.swap i j).1 i = (1 : S n).1 i := H3,
replace H4: (equiv.swap i j).1 i = j := H4,
rw[eq_comm] at H4,
have H6: (1 : S n).to_fun i = j,
rw[eq.trans H4 H3],
exact a_h_h.1 H6,
intros,
simp[g] at a,
exact a,
intros,
simp[g],
existsi (a * (equiv.swap i j)⁻¹),
rw[_root_.mul_assoc],
rw[mul_left_inv],
simp,
intros,
simp[g],
rw[_root_.mul_assoc],
have H7: equiv.swap i j * (equiv.swap i j)⁻¹ = (1: S n),
rw[mul_right_inv],
refl,
have H8 : (equiv.swap i j)⁻¹ = equiv.swap i j ,
refl,
rw[H8] at H7,
rw[H7],
simp,
intros,
simp,
end
theorem not_bij_not_inj {α : Type* } [s : fintype α ] {f : α  → α} (h: ¬function.bijective f ) : ¬function.injective f:= sorry 

#check eq.trans



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
             (λ (x : S n),
                e (x.to_fun) *
                  finset.prod (finset.attach finset.univ)
                    (λ (x_1 : {x // x ∈ finset.univ}), A (x.to_fun (x_1.val)) (y (x_1.val) _)))) = 
                     finset.sum (finset.univ : finset (fin n → fin n))
      (λ (y : fin n → fin n),
         finset.prod (finset.univ : finset( fin n) ) (λ (x : fin n), B (y x) x) *
           finset.sum finset.univ
             (λ (x : S n),
                e (x.to_fun) *
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
have H13: finset.sum finset.univ (λ (x : S n),
           e (x.to_fun) *
             finset.prod (finset.attach finset.univ)
               (λ (x_1 : {x // x ∈ finset.univ}), A (x.to_fun (x_1.val))
                (a (x_1.val) (finset.mem_univ _))))= finset.sum finset.univ (λ (x : S n),
           e (x.to_fun) *
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
               (λ (x : S n), e (x.to_fun) * finset.prod finset.univ (λ (x_1 : fin n),
                A (x.to_fun x_1) (y x_1)))) = 
        finset.sum (finset.univ : finset (S n))
        (λ y,
           finset.prod finset.univ (λ (x : fin n), B (y.1 x) x) *
             finset.sum finset.univ
               (λ (x : S n), e (x.to_fun) * finset.prod finset.univ (λ (x_1 : fin n),
                A (x.to_fun x_1) (y.1 x_1)))),

let t : Π a ∈ (finset.univ : finset (S n)), fin n → fin n  :=
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
exact (finset.mem_filter.1 H).2,
existsi @equiv.of_bijective _ _ b H22,
exact eq.symm (equiv.of_bijective_to_fun _),
rw[H21],
simp only[M1],
simp only[mul_comm],
simp only[_root_.mul_assoc],
rw[← finset.mul_sum],
rw[← det],
have H3: finset.sum (finset.filter (λ (f : fin n → fin n), ¬function.bijective f) finset.univ)
        (λ (y : fin n → fin n),
           finset.prod finset.univ (λ (x : fin n), B (y x) x) *
             finset.sum finset.univ
               (λ (x : S n), e (x.to_fun) * 
               finset.prod finset.univ (λ (x_1 : fin n), A (x.to_fun x_1) (y x_1)))) = 0,
conv
begin 
to_rhs,
rw[← @finset.sum_const_zero _ _ (finset.filter (λ (f : fin n → fin n), ¬function.bijective f) finset.univ) _],
end,
refine finset.sum_congr rfl _,
intros,
have H4: finset.sum finset.univ
        (λ (x_1 : S n),
           e (x_1.to_fun) * finset.prod finset.univ (λ (x_1_1 : fin n), A (x_1.to_fun x_1_1) (x x_1_1))) =
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
      (λ (x_1 : S n), e (x_1.to_fun) * finset.prod finset.univ (λ (x_1_1 : fin n), W (x_1.to_fun x_1_1)  x_1_1)) =
    0,
    rw[← det],
    rw[M2],
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
