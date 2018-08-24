import algebra.euclidean_domain ring_theory.ideals 
universes u v
variables {α : Type u} {β : Type v} [comm_ring α] {a b : α}
open set function
local attribute [instance] classical.prop_decidable

class is_principal_ideal {α : Type u} [comm_ring α] (S : set α) : Prop := 
(principal : ∃ a : α, S = {x | a ∣ x})

class principal_ideal_domain (α : Type*) extends integral_domain α :=
(principal : ∀ (S : set α) [is_ideal S], is_principal_ideal S)

namespace is_principal_ideal.to_is_ideal

protected lemma zero (S : set α) [is_principal_ideal S] : (0 : α) ∈ S := 
begin
  cases is_principal_ideal.principal S,
  rw[h],
  have H1 : w ∣ 0,
  { exact dvd_zero w },
  exact H1 
end

protected lemma add {S : set α} [is_principal_ideal S] : ∀ {x y : α}, x ∈ S → y ∈ S → x + y ∈ S :=
begin
  intros,
  cases is_principal_ideal.principal S,
  rw[h],
  rw[h] at a_1,
  rw[h] at a,
  exact dvd_add a a_1,
end
protected lemma smul {S : set α} [is_principal_ideal S] : ∀ (c : α) {x : α}, x ∈ S → c • x ∈ S :=
begin 
  intros,
  cases is_principal_ideal.principal S,
  rw[h],
  show c * x ∈ {x : α | w ∣ x},
  rw[h] at a,
  exact dvd_mul_of_dvd_right a c,
end
instance is_principal_ideal.to_is_ideal {α : Type u} [comm_ring α] (S : set α) [is_principal_ideal S] : is_ideal S :=
{ to_is_submodule :=
begin 
split,
{ exact is_principal_ideal.to_is_ideal.zero S},
{ exact @is_principal_ideal.to_is_ideal.add _ _ _ _ },
{ exact @is_principal_ideal.to_is_ideal.smul _ _ _ _ },
end
} 
end is_principal_ideal.to_is_ideal

instance euclidean_domain.to_principal_ideal_domain {α : Type u} [euclidean_domain α]
: principal_ideal_domain α :=
{ principal :=
  begin
    intros,
    resetI,
    split,
    have H1 : well_founded (euclidean_domain.r : α → α → Prop),
    { exact euclidean_domain.r_well_founded α },
    let L := set.diff S {x | x = 0},
    by_cases L ≠ ∅ ,
    { have H6 : well_founded.min H1 L h ∈ S,
        { have h : well_founded.min H1 L h ∈ L,
          { exact well_founded.min_mem H1 L h },
        simp[L] at h,
        unfold set.diff at h,
        exact h.1,
        },
      existsi well_founded.min H1 L h,
      have H4 : S ⊆ {x : α | well_founded.min H1 L h ∣ x},
      { intro x,
        intro,
        show well_founded.min H1 L h ∣ x,
        have H4 : (well_founded.min H1 L h) * euclidean_domain.quotient x (well_founded.min H1 L h)
        + euclidean_domain.remainder x (well_founded.min H1 L h) = x,
        { exact euclidean_domain.quotient_mul_add_remainder_eq x (well_founded.min H1 L h) },
        rw[add_comm] at H4,
        have H5 : euclidean_domain.remainder x (well_founded.min H1 L h) = x - well_founded.min H1 L h * euclidean_domain.quotient x (well_founded.min H1 L h),
        { rw[eq_add_neg_of_add_eq H4], refl },
        have H7 : well_founded.min H1 L h * euclidean_domain.quotient x (well_founded.min H1 L h) ∈ S,
        { exact is_ideal.mul_right H6 },
        have H8 : euclidean_domain.remainder x (well_founded.min H1 L h) ∈ S,
        { rw[H5], exact is_ideal.sub a H7 },
        by_cases h' :  euclidean_domain.remainder x (well_founded.min H1 L h) = 0,
        { rw[h'] at H4,
          simp at H4,
          exact dvd.intro (euclidean_domain.quotient x (well_founded.min H1 L h)) H4 },
        replace h' : euclidean_domain.remainder x (well_founded.min H1 L h) ≠ 0 := h',
        have H9 : euclidean_domain.remainder x (well_founded.min H1 L h) ∈ L,
        { simp[L],
          unfold set.diff,
          exact ⟨ H8, 
          begin 
            intro,
            have h : euclidean_domain.remainder x (well_founded.min H1 L h) = 0,
            { exact a_1},
            contradiction,
          end⟩ } ,
          have H10 : ¬  (well_founded.min H1 L h) = 0,
          { exact (well_founded.min_mem H1 L h).2 },
          replace H10 : well_founded.min H1 L h ≠  0 := H10,
          have H11 : euclidean_domain.r (euclidean_domain.remainder x (well_founded.min H1 L h)) (well_founded.min H1 L h),
          { exact euclidean_domain.remainder_lt x H10 },
          have H12 : ¬ euclidean_domain.r (euclidean_domain.remainder x (well_founded.min H1 L h)) (well_founded.min H1 L h),
          { exact well_founded.not_lt_min H1 L h H9 },
          contradiction },
       have H5 : {x : α | well_founded.min H1 L h ∣ x} ⊆ S,
       { intro x,
         intro,
         have H6 : ∃ c : α , x = c * well_founded.min H1 L h ,
         { exact exists_eq_mul_left_of_dvd a },
         cases H6,
         rw[H6_h],
         exact is_ideal.mul_left H6 },
        exact set.subset.antisymm H4 H5 },
    { simp at h,
      have h3 : S ≠ ∅ → L = ∅ → S = {x : α | x = 0},
      { simp [L, set.ext_iff, set.diff, iff_def, is_ideal.zero S] {contextual := tt}, 
      finish }, 
      have h4 : ∃ x, x ∈ S,
      { existsi (0 : α),
       exact is_ideal.zero S },
      have h5 : S ≠ ∅ ,
      { exact ne_empty_iff_exists_mem.2 h4} ,
      have h6 :  S = {x : α | x = 0},
      { exact h3 h5 h },
      existsi (0 : α),
      rw[h6],
      congr,
      funext,
      apply propext,
      split,
      { intro,
        rw[a]
      },
     intro,
     have h6 : ∃ a, x = 0 * a,
     {  exact exists_eq_mul_right_of_dvd a },
     cases h6,
     simp[h6_h],
    }
      
end
 

}
#check dvd.elim 
--#check set.subset.antisymm
#check ne_empty_iff_exists_mem