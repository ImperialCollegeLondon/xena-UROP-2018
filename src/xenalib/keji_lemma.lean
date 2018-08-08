import data.finset
import algebra.big_operators
import data.fintype

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
∀ a₁ a₂ a₃: (↑s : set β), eqv g h₄ h₅ a₁ a₂ → eqv g h₄ h₅ a₂ a₃ → eqv g h₄ h₅ a₁ a₃
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


lemma sum_keji {α β : Type*} [add_comm_monoid α] [decidable_eq β] {f : β → α}
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
