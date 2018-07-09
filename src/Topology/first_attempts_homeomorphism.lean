import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space


universes u v w

open set filter lattice classical

#print definition set


#check empty 
def empty_set_topology : topological_space empty := 
{
is_open := λ (a : set empty),
true, is_open_univ := begin trivial, end,
is_open_inter := begin intros h1 h2 h3 h4, trivial end,
is_open_sUnion := begin intros h1 h2, trivial end
} 
#print univ
#check empty_set_topology.is_open 

#print set

definition is_open_sets {α : Type u} (is_open : set α → Prop) :=
  is_open univ ∧ (∀s t, is_open s → is_open t → is_open (s ∩ t)) ∧ (∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

definition is_to_top {α : Type u} (is_open : set α → Prop) (H : is_open_sets (is_open)) : topological_space α :=
{ is_open := is_open,
  is_open_univ := H.left,
  is_open_inter := H.right.left,
  is_open_sUnion := H.right.right
}

definition top_to_is {α : Type u} (T : topological_space α) : is_open_sets (T.is_open) :=
⟨T.is_open_univ,T.is_open_inter,T.is_open_sUnion⟩



--8.7 defn homeo, 8.12 continuity by bases, ex 8.4, 10.11 product topology 

definition I : set ℝ := λ x, x ≤ 1 ∧ x ≥ 0


--We could define these here, but they have been defined in the core
definition is_injective {α : Type u} {β : Type v} (f : α → β) :=  ∀ x y : α, f x = f y → x = y
definition is_surjective {α : Type u} {β : Type v} (f : α → β)  := ∀ b : β, ∃ x : α, f(x) = b 
definition is_bijective {α : Type u} {β : Type v} (f : α → β)  := is_injective f ∧ is_surjective f

--Or we could define things using structures:
structure injection (α : Type u) (β : Type v) :=
(f : α → β)
(f_is_injective : ∀ x y : α, f x = f y → x = y)
structure surjection (α : Type u) (β : Type v) :=
(f : α → β)
(f_is_surjective :  ∀ b : β, ∃ x : α, f(x) = b)
structure bijection (α : Type u) (β : Type v) :=
(f : α → β)
(f_is_injective : ∀ x y : α, f x = f y → x = y)
(f_is_surjective :  ∀ b : β, ∃ x : α, f(x) = b)

--These can be swapped between
definition bij_to_is {α : Type u} {β : Type v} (B : bijection α β) : is_bijective B.1 := ⟨B.2 , B.3⟩
definition is_to_bij {α : Type u} {β : Type v} (f : α → β) (H : is_bijective f) : bijection α β := 
{ f := f,
  f_is_injective := H.1,
  f_is_surjective := H.2
}


--First we must show that bijection is equivalent to having a two-sided inverse
def two_sided_inverse {α : Type u} {β : Type v} (g : β → α) (f : α → β) : Prop := function.left_inverse g f ∧ function.right_inverse g f

theorem two_sided_inverse_iff_bijection {α : Type u} {β : Type v} {f : α → β} : (∃ g : β → α, two_sided_inverse g f) ↔ function.bijective f :=
begin
  admit,
end

--Here we use the definition bijective from the core.
definition open_mapping {α : Type u} {β : Type v} [topological_space α] [topological_space β] (f : α → β) := ∀s : set α, is_open s → is_open (set.image f s) 

definition is_homeomorphism {α : Type u} {β : Type v} [topological_space α] [topological_space β] (f : α → β) := continuous f ∧ function.bijective f ∧ open_mapping f 
-- Square brackets okay?
definition is_homeomorphic_to {α : Type u} {β : Type v} (X :topological_space α) (Y : topological_space β) := ∃ f : α → β, is_homeomorphism f 

structure homeomorphism1 {α : Type u} {β : Type v} (X : topological_space α) (Y : topological_space β) :=
(f : α → β)
(is_homeomorphism : is_homeomorphism f)
 

definition id_is_homeomorphism {α : Type u} {X : topological_space α} : homeomorphism1 X X := {f := id,
is_homeomorphism := 
begin
unfold is_homeomorphism,
split,
unfold continuous,
unfold set.preimage,
intros s H1,
unfold id,
exact H1,
split,
apply function.bijective_id,
unfold open_mapping,
intros s H,
unfold set.image,
unfold id,
simp,
assumption,
end
}


theorem homeomorphism_is_reflexive : reflexive (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin 
unfold reflexive,
intro top,
unfold is_homeomorphic_to,
existsi id,
exact id_is_homeomorphism.2,
end

--FOR THIS IT WOULD BE NICE TO HAVE AN INVERSE FUNCTION EXPLICIT
theorem homeomorphism_is_symmetric : symmetric (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin
unfold symmetric,
intros X Y,
unfold is_homeomorphic_to,
admit,
end

theorem homeomorphism_is_equiv_rel : equivalence (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin
admit,
end
--We require β : Sort v and two topological spaces of type β 
--Sort?


--def reflexive := ∀ x, x ≺ x

--def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

--def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

--def equivalence := reflexive r ∧ symmetric r ∧ transitive r