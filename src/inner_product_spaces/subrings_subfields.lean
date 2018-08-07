import algebra.field data.set

universe u

class is_subring {R : Type u} [ring R] (s : set R) : Prop :=
(one_mem : (1 : R) ∈ s) 
(sub_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x - y ∈ s)
(mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s)

open is_subring set

lemma zero_in_subring {R : Type u} [ring R] {s : set R} [is_subring s] :
(0 : R) ∈ s := eq.subst (sub_self (1 : R)) (sub_mem (one_mem s) (one_mem s))

lemma neg_in_subring {R : Type u} [ring R] {s : set R} [is_subring s] {x : R}:
x ∈ s → -x ∈ s :=
begin
intros hx,
have H : 0 - x ∈ s,
    exact sub_mem zero_in_subring hx,
rw zero_sub at H,
exact H,
end

lemma add_mem  {R : Type u} [ring R] {s : set R} [is_subring s] {x y : R} :
x ∈ s → y ∈ s → x + y ∈ s := λ hx hy, eq.subst (sub_neg_eq_add x y) (sub_mem hx (neg_in_subring hy))

instance sub_ring_to_ring {R : Type u} [ring R] (s : set R) [is_subring s] : ring s :=
{
add := λ (a b : s), ⟨a.val + b.val, add_mem a.property b.property⟩, 
add_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq (add_assoc a b c),
zero := ⟨0, zero_in_subring⟩, 
zero_add := assume ⟨a, _⟩, subtype.eq (zero_add a), 
add_zero := assume ⟨a, _⟩, subtype.eq (add_zero a),
neg := λ (a : s), ⟨ -a.val, neg_in_subring a.property⟩ ,
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
