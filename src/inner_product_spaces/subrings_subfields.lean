import algebra.field data.set

universe u

class is_subring {R : Type u} [ring R] (s : set R) : Prop :=
(one_mem : (1 : R) ∈ s) 
(sub_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x - y ∈ s)
(mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s)

open is_subring set

namespace is_subring

lemma zero_mem {R : Type u} [ring R] {s : set R} [is_subring s] :
(0 : R) ∈ s := eq.subst (sub_self (1 : R)) (sub_mem (one_mem s) (one_mem s))

lemma neg_mem {R : Type u} [ring R] {s : set R} [is_subring s] {x : R}:
x ∈ s → -x ∈ s :=
begin
intros hx,
have H : 0 - x ∈ s,
    exact sub_mem zero_mem hx,
rw zero_sub at H,
exact H,
end

lemma add_mem  {R : Type u} [ring R] {s : set R} [is_subring s] {x y : R} :
x ∈ s → y ∈ s → x + y ∈ s := λ hx hy, eq.subst (sub_neg_eq_add x y) (sub_mem hx (neg_mem hy))

instance subring_to_ring {R : Type u} [ring R] (s : set R) [is_subring s] : ring s :=
{
add := λ (a b : s), ⟨a.val + b.val, add_mem a.property b.property⟩, 
add_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (add_assoc a b c),
zero := ⟨0, zero_mem⟩, 
zero_add := assume ⟨a, _⟩, subtype.eq (zero_add a), 
add_zero := assume ⟨a, _⟩, subtype.eq (add_zero a),
neg := λ (a : s), ⟨ -a.val, neg_mem a.property⟩ ,
add_left_neg := assume ⟨a, _⟩, subtype.eq (add_left_neg a),
add_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq (add_comm a b),
mul := λ (a b : s), ⟨a.val * b.val, mul_mem a.property b.property⟩,
mul_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (mul_assoc a b c),   
one := ⟨1, one_mem s⟩,
one_mul := assume ⟨a, _⟩, subtype.eq (one_mul a), 
mul_one := assume ⟨a, _⟩, subtype.eq (mul_one a),
left_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (left_distrib a b c),
right_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (right_distrib a b c),
} 

end is_subring

class is_subfield {F : Type u} [field F] (s : set F) : Prop :=
(one_mem : (1 : F) ∈ s)
(sub_mem : ∀ {x y : F}, x ∈ s → y ∈ s → x - y ∈ s)
(mul_mem : ∀ {x y : F}, x ∈ s → y ∈ s → x * y ∈ s)
(inv_mem : ∀ {x : F}, x ∈ s → x⁻¹ ∈ s)

open is_subfield

namespace is_subfield

lemma zero_mem {F : Type u} [field F] {s : set F} [is_subfield s] :
(0 : F) ∈ s := eq.subst (sub_self (1 : F)) (sub_mem (one_mem s) (one_mem s))

lemma neg_mem {R : Type u} [field R] {s : set R} [is_subfield s] {x : R}:
x ∈ s → -x ∈ s :=
begin
intros hx,
have H : 0 - x ∈ s,
    exact sub_mem zero_mem hx,
rw zero_sub at H,
exact H,
end

lemma add_mem {F : Type u} [field F] {s : set F} [is_subfield s] {x y : F} :
x ∈ s → y ∈ s → x + y ∈ s := λ hx hy, eq.subst (sub_neg_eq_add x y) (sub_mem hx (neg_mem hy))

instance subfield_to_field {F : Type u} [field F] (s : set F) [is_subfield s] : field s :=
{
add := λ (a b : s), ⟨a.val + b.val, add_mem a.property b.property⟩, 
add_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (add_assoc a b c),
zero := ⟨0, zero_mem⟩, 
zero_add := assume ⟨a, _⟩, subtype.eq (zero_add a), 
add_zero := assume ⟨a, _⟩, subtype.eq (add_zero a),
neg := λ (a : s), ⟨ -a.val, neg_mem a.property⟩ ,
add_left_neg := assume ⟨a, _⟩, subtype.eq (add_left_neg a),
add_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq (add_comm a b),
mul := λ (a b : s), ⟨a.val * b.val, mul_mem a.property b.property⟩,
mul_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (mul_assoc a b c),   
one := ⟨1, one_mem s⟩,
one_mul := assume ⟨a, _⟩, subtype.eq (one_mul a), 
mul_one := assume ⟨a, _⟩, subtype.eq (mul_one a),
left_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (left_distrib a b c),
right_distrib := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (right_distrib a b c),
inv := λ (a : s), ⟨a.val⁻¹, inv_mem a.property⟩,   
zero_ne_one := begin apply (iff_false_left zero_ne_one).mp, simp, exact F, apply_instance, end,
mul_inv_cancel := assume ⟨a, _⟩, λ h, subtype.eq (mul_inv_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
inv_mul_cancel := assume ⟨a, _⟩, λ h, subtype.eq (inv_mul_cancel ((iff_false_left (not_not_intro h)).mp (begin dunfold ne, rw auto.not_not_eq, apply subtype.ext, end))),
mul_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq (mul_comm a b),
}

end is_subfield
