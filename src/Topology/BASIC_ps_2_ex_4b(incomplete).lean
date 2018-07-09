import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

universe u

open set filter lattice classical

#print definition set


#check empty 
def empty_topology : topological_space empty := 
{
is_open := λ (a : set empty),
true, is_open_univ := begin trivial, end,
is_open_inter := begin intros h1 h2 h3 h4, trivial end,
is_open_sUnion := begin intros h1 h2, trivial end
} 
#print univ
#check empty_topology.is_open 


--Exercise 4. Let X be a non-empty set and let T1 and T2 be topologies on X. 1. Must T1 ∩ T2 be a topology on X? 2. Must T1 ∪ T2 be a topology on X?

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

theorem exercisefoura {α : Type u} {T1_sets T2_sets : set α → Prop} : is_open_sets T1_sets → is_open_sets T2_sets → is_open_sets (λ (a : set α), and (T1_sets a) (T2_sets a)) :=
begin
intros H1 H2,
unfold is_open_sets,
split,
exact ⟨H1.left, H2.left⟩,
split,
intros s t H3 H4,
exact ⟨H1.right.left s t H3.left H4.left, H2.right.left s t H3.right H4.right⟩,
intros I H3,
split,
have H4 : ∀ (t : set α), t ∈ I → T1_sets t,
intros A H5,
exact (H3 A H5).left,
exact H1.right.right I H4,
have H4 :  ∀ (t : set α), t ∈ I → T2_sets t,
intros A H5,
exact (H3 A H5).right,
exact H2.right.right I H4,
end

inductive zeroonetwo : Type  -- use Type to work instead of Type u 
| zero : zeroonetwo 
| one : zeroonetwo
| two : zeroonetwo



open zeroonetwo
#print univ



def collection_one : set zeroonetwo  → Prop := λ s, s = ∅ ∨ s = {one, two} ∨ s = {zero, one, two}
def collection_two : set zeroonetwo → Prop := λ s, s = ∅ ∨ s = {zero, one} ∨ s = {zero, one, two} 

def T1 : topological_space zeroonetwo := {
is_open := collection_one,
is_open_univ := begin have : (univ : set zeroonetwo) = {zero, one, two}, apply set.ext, assume x, cases x; simp, rewrite this, unfold collection_one, have obv : {zero, one, two} = {zero, one, two}, trivial, exact or.inr (or.inr obv) end,
is_open_inter := begin intros s t H1 H2, unfold collection_one at H1 H2, cases H1, cases H2, simp *,
 unfold collection_one, cc, cases H2, simp *, unfold collection_one, cc, simp *,
  unfold collection_one, cc, cases H1, cases H2, simp *, unfold collection_one, cc,
   cases H2, simp [*, collection_one], cc, simp [*, collection_one],
    have obv2 : insert two {one} ∩ insert two (insert one {zero}) = insert two {one}, unfold insert, rw inter_eq_self_of_subset_left, assume x : zeroonetwo, finish, exact or.inr (or.inl obv2), 
    cases H2, simp [*, collection_one], finish, cases H2, simp[*, collection_one], have obv3 : insert two (insert one {zero}) ∩ insert two {one} = insert two {one}, unfold insert, rw inter_eq_self_of_subset_right, assume x : zeroonetwo, finish, exact or.inr (or.inl obv3),
    simp [*, collection_one], finish, end,
is_open_sUnion := by admit 
 }

def T2 : topological_space zeroonetwo := {
    is_open := collection_two,
    is_open_univ := by admit,
    is_open_inter := by admit,
    is_open_sUnion := by admit
}

example : zero ∈ ({zero, one} : set zeroonetwo) := by simp


theorem exercisefourb : ¬ ∀ {α : Type } {T1_sets T2_sets : set α → Prop}, (is_open_sets T1_sets → is_open_sets T2_sets → is_open_sets (λ (a : set α), or (T1_sets a) (T2_sets a)) :=
begin
intro H1,
have is_topology : is_open_sets (λ (a : set zeroonetwo), collection_one a ∨ collection_two a),
exact H1 (top_to_is T1) (top_to_is T2),
unfold is_open_sets at is_topology,
have S : collection_one {one, two},
unfold collection_one, cc,
have T : collection_two {zero, one},
unfold collection_two, cc,
have M : collection_one ({one, two} ∩ {zero, one}) ∨ collection_two ({one, two} ∩ {zero, one}),
exact is_topology.right.left {one,two} {zero, one} (or.inl S) (or.inr T),
have obvious : {one, two} ∩ {zero, one} = {one}, 
apply set.ext, assume x : zeroonetwo, cases x, finish, split, rw mem_inter_eq one {one,two} {zero, one}, simp, exact mem_singleton _,
simp, finish,
rw obvious at M, 
cases M,
admit,
end
