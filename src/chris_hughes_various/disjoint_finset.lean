import data.finset

namespace finset
variable {α : Type*}

def disjoint (s t : finset α) : Prop := ∀ ⦃a⦄, a ∈ s → a ∈ t → false

theorem disjoint.symm {s t : finset α} (d : disjoint s t) : disjoint t s
| a i₂ i₁ := d i₁ i₂

@[simp] theorem disjoint_comm {s t : finset α} : disjoint s t ↔ disjoint t s :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := iff.rfl

theorem disjoint_right {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
disjoint_comm

theorem disjoint_iff_ne {s t : finset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : finset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t
| x m₁ := d (h m₁)

theorem disjoint_of_subset_right {s t u : finset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t
| x m m₁ := d m (h m₁)

@[simp] theorem empty_disjoint (l : finset α) : disjoint ∅ l
| a := (not_mem_empty a).elim

@[simp] theorem singleton_disjoint [decidable_eq α] {l : finset α} {a : α} : disjoint (singleton a) l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp] theorem disjoint_singleton [decidable_eq α] {l : finset α} {a : α} : disjoint l (singleton a) ↔ a ∉ l :=
by rw disjoint_comm; simp

@[simp] theorem disjoint_insert_left [decidable_eq α] {a : α} {s t : finset α} :
  disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]; refl

@[simp] theorem disjoint_insert_right [decidable_eq α] {a : α} {s t : finset α} :
  disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint_comm.trans $ by simp [disjoint_insert_left]

theorem inter_eq_zero_iff_disjoint [decidable_eq α] {s t : finset α} : s ∩ t = ∅ ↔ disjoint s t :=
by rw ← subset_empty; simp [subset_iff, disjoint]

@[simp] theorem disjoint_union_left [decidable_eq α] {s t u : finset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right [decidable_eq α] {s t u : finset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_val {s t : finset α} : multiset.disjoint s.1 t.1 ↔ disjoint s t :=
by simp [disjoint, multiset.disjoint, mem_def]

@[simp] theorem card_disjoint_union [decidable_eq α] {s t : finset α} :
    disjoint s t → card (s ∪ t) = card s + card t :=
finset.induction_on s (by simp) $ begin simp {contextual := tt} end

end finset