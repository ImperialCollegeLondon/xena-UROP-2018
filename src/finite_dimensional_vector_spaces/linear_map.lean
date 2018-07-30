import xenalib.Ellen_Arlt_matrix_rings 
import algebra.big_operators
import data.set.finite
import algebra.module 
import data.finsupp
import algebra.group
import linear_algebra.basic
import data.fintype
import data.equiv.basic
import linear_algebra.linear_map_module
import algebra.pi_instances

-- reserve infix ` ^ `: 50


-- class has_map (R : Type) (n : nat) [ring R] := (char : nat → fin n → R)
-- infix ^ := has_map.char

-- R^n
universe u
variables {α : Type u}
variables {β : Type*} [add_comm_group α] [add_comm_group β]

/-- Predicate for group homomorphism. -/
class is_add_group_hom (f : α → β) : Prop :=
(add : ∀ a b : α, f (a + b) = (f a) + (f b))
namespace is_add_group_hom
variables (f : α → β) [is_add_group_hom f]

theorem zero : f 0 = 0 :=
add_self_iff_eq_zero.1 $ by simp [(add f 0 _).symm]

theorem inv (a : α) : f(-a)  = -(f a) :=
eq.symm $ neg_eq_of_add_eq_zero $ by simp [(add f a (-a)).symm, zero f]

instance id : is_add_group_hom (@id α) :=
⟨λ _ _, rfl⟩

instance comp {γ} [add_comm_group γ] (g : β → γ) [is_add_group_hom g] :
  is_add_group_hom (g ∘ f) :=
⟨λ x y, calc
  g (f (x + y)) = g (f x + f y)       : by rw add f
  ...           = g (f x) + g (f y)   : by rw add g⟩

end is_add_group_hom

definition has_space (R : Type) (n : nat) := (fin n) → R

def add (R : Type) (n : nat) [ring R] := 
λ (a b :has_space R n), (λ i, (a i) +(b i))

def smul {R : Type} {n : nat} [ring R] (s : R) (rn : has_space R n) : 
has_space R n := λ I, s * (rn I)

theorem add__assoc {R : Type} {n : nat} [ring R] (a b c :(fin n) → R):add R n (add R n a b) c = add R n a (add R n b c):=
begin 
unfold add,
funext,
simp,
end
theorem add__comm {R : Type} {n : nat} [ring R] (a b :(fin n) → R):
 add R n a b =add R n b a :=
begin 
unfold add,
funext,
exact add_comm (a i) (b i),
end
def zero (R : Type) (n : nat) [ring R]: has_space R n := λ (i:fin n),(0 :R)
#check zero
theorem zero__add {R : Type} {n : nat} [ring R] (a:has_space R n): add R n (zero R n) a = a:=
begin 
unfold add,
funext,
unfold zero,
simp,
end

def neg (R : Type) (n : nat) [ring R]:= λ (a:has_space R n),(λ i, -(a i))
theorem add__left__neg {R : Type} {n : nat} [ring R] (a :has_space R n): add R n (neg R n a) a = zero R n:=
begin 
unfold add,
unfold zero,
funext,
unfold neg,
simp,
end 

def add__zero {R : Type} {n : nat} [ring R] (a :has_space R n): add R n a (zero R n) =a:=
begin
unfold add,
funext,
unfold zero,
simp,
end

instance (R : Type) [ring R] (n : nat) : add_comm_group (has_space R n) := 
{add:=add R n,
add_assoc := add__assoc,
zero := zero R n,
zero_add:= zero__add,
neg:=neg R n,
add_left_neg:= add__left__neg, 
add_zero:= add__zero ,
add_comm:= add__comm,
}

namespace R_module
variables (R : Type) (n : nat)
variables [ring R] --[module R (has_space R n)]

theorem smul_add (s : R) (rn rm : has_space R n) : 
    smul s (add R n rn rm) = add R n (smul s rn) (smul s rm) := 
-- s • (rn + rm) = s • rn + s • rm 
    begin
      apply funext,
      intro,
      unfold smul add,
      apply mul_add,
    end 

theorem add_smul (s t : R) (rn: has_space R n): 
    smul (s + t) rn = add R n (smul s rn) (smul t rn) := 
    begin
      apply funext,
      intro,
      unfold smul add,
      apply add_mul,
    end

theorem mul_smul (s t : R) (rn : has_space R n): 
    smul (s * t) rn = smul s (smul t rn) :=
    begin
      apply funext,
      intro,
      unfold smul,
      apply mul_assoc,
    end

theorem one_smul (rn : has_space R n): 
    smul (1 : R) rn = rn :=
    begin
      apply funext,
      intro,
      unfold smul,
      apply one_mul,
    end
end R_module

#check has_scalar

instance (R : Type) [ring R] (n : nat) : has_scalar R (has_space R n) :=
{ 
    smul := smul
}


instance {R : Type} {n : nat} [ring R] 
: module R (has_space R n) :=
{   
    smul_add := R_module.smul_add R n,
    add_smul := R_module.add_smul R n,
    mul_smul := R_module.mul_smul R n,
    one_smul := R_module.one_smul R n,
}



namespace map_matrix

definition matrix_to_map {R : Type} [ring R] {a b : nat} (M : matrix R a b) :
(has_space R a) → (has_space R b) := λ v ,(λ i,finset.sum finset.univ (λ K, (v K) *M K i ) )


instance hg {R : Type} [ring R] {a b : nat} (M : matrix R a b) : is_add_group_hom (matrix_to_map M) := 
⟨begin
intros,
funext,
unfold matrix_to_map,

show (finset.sum finset.univ (λ (K : fin a), (a_1 K + b_1 K)  * M K i) =_),
conv in ( (a_1 _ + b_1 _) * M _ i)
  begin
    rw [add_mul],
  end,

rw finset.sum_add_distrib,
refl,
end⟩ 

theorem smul_ {R: Type} [ring R] {a b : nat} (M : matrix R a b): ∀ (c : R) (x : has_space R a), matrix_to_map M (smul c x) = smul c  (matrix_to_map M x):=
begin 
intros,
unfold matrix_to_map,
funext,
unfold smul,
rw [finset.mul_sum],
simp[mul_assoc],
end

def module_hom {R: Type} [ring R] {a b : nat} (M : matrix R a b) : 
  @is_linear_map R _ _ _ _ _ (matrix_to_map M) :=
 { add:= 
 begin 
exact is_add_group_hom.add _,
 end,
 smul:= smul_ _,
}

def matrix_to_linear_map {R : Type} [ring R] {a b : nat} (M : matrix R a b) : 
  (@linear_map R (has_space R a)  (has_space R b) _ _ _) :=
⟨matrix_to_map M, module_hom M⟩ 

def e (R : Type) [ring R] (a: nat) (i: fin a): has_space R a:= λ j, if i =j then 1 else 0

definition map_to_matrix {R : Type} [ring R] {a b : nat} (f: @linear_map R (has_space R a) 
 (has_space R b) _ _ _) : matrix R a b :=
    λ i j, f.1 (e R a i) j


theorem finset.sum_single {α : Type*} [fintype α]
  {β : Type*} [add_comm_monoid β]
  (f : α → β) {i : α}
  (h : ∀ (j : α), i ≠ j → f j = 0) :
f i = finset.sum finset.univ (λ (K : α), f K) :=
begin
  have H : finset.sum (finset.singleton i) (λ (K : α), f K)
    = finset.sum finset.univ (λ (K : α), f K),
  from finset.sum_subset (λ _ _, finset.mem_univ _)
    (λ _ _ H, h _ $ mt (λ h, finset.mem_singleton.2 h.symm) H),
  rw [← H, finset.sum_singleton]
end 

theorem apply_function_to_sum {R : Type}[ring R] {n p : nat} (f: fin n → has_space R p ) (i : fin p ): 
(finset.sum finset.univ (λ (K : fin n),f K)) i = finset.sum finset.univ (λ (K : fin n), f K i):=
begin
rw finset.sum_hom (λ (v: has_space R p), v i ) _,
intros,
simp,
refl,
end

theorem span {R : Type} {n : nat} [ring R] (v : has_space R n): 
  v = finset.sum finset.univ (λ K, smul (v K) (e R n K)):=
begin 
funext,
rw [apply_function_to_sum (λ i, smul (v i) (e R n i))],
simp,
unfold smul,
  have H1 : ∀ (j : fin n), x ≠ j → v j * (e R n j) x = 0,
    intros,
    unfold e,
    split_ifs,
      exact false.elim (a h.symm),
    simp,
  have H2: finset.sum finset.univ (λ (K : fin n), v K * e R n K x) = v x * e R n x x,
    have Htemp := finset.sum_single (λ (K:fin n), v K * e R n K x ) H1,
    rw ←Htemp,
  rw H2,
  unfold e,
  split_ifs,
  simp,
  simp,  
end 

theorem equiv_one {R : Type} [ring R] {a b : nat} (f : (@linear_map R (has_space R a) 
  (has_space R b) _ _ _)) :
    matrix_to_map (map_to_matrix f ) = f := 
begin
funext,
unfold map_to_matrix,
unfold matrix_to_map,
conv begin
to_rhs,
rw [span v],
end,
rw [← finset.sum_hom f _],
swap 3,
exact is_linear_map.zero f.2,
swap 2,
exact f.2.add,
rw[apply_function_to_sum (λ j,f (smul (v j) (e R a j)))],
simp,
show _ = finset.sum finset.univ (λ (K : fin a), f ((v K) • (e R a K)) i),
congr,
funext,
rw[( linear_map.is_linear_map_coe).smul],
refl,
end 

#check is_linear_map
theorem equiv_two {R : Type} [ring R] {p b : nat} (M : matrix R p b):
  map_to_matrix ⟨ matrix_to_map M, module_hom M⟩  = M := 
  begin
   funext,
   unfold map_to_matrix,
   show (matrix_to_map M) (e R p i) j =_,
   unfold matrix_to_map,
    have H1: ∀ (K : fin p), i ≠ K →  e R p i K * M K j = 0,
    intros,
    unfold e,
    split_ifs,
    exact false.elim (a h),
    simp,
    have H2: finset.sum finset.univ (λ (K : fin p), e R p i K * M K j) = e R p i i * M i j,
       have Htemp := finset.sum_single (λ (K : fin p), e R p i K * M K j) H1,
    rw ← Htemp,
    rw H2,
    unfold e,
    split_ifs,
    simp,
    simp,
  end

def matrix_to_linear_map_equiv {R : Type} [ring R] {a b : nat} :
  equiv  (matrix R a b)  (@linear_map R (has_space R a)  (has_space R b) _ _ _):= 
    {to_fun := matrix_to_linear_map,
    inv_fun := map_to_matrix,
    right_inv:= 
    begin 
     unfold function.right_inverse,
     unfold function.left_inverse,
     intros,
    apply subtype.eq,
    dsimp,
    exact equiv_one x, 
    end,
    left_inv:= 
    begin 
    unfold function.left_inverse,
    intros,
    exact equiv_two x,
    end  
   }

instance  {R : Type} [ring R] {a b : nat}:  is_add_group_hom (@matrix_to_linear_map R _ a b):=
  { add:= 
  begin 
  intros,
  unfold matrix_to_linear_map,
  apply linear_map.ext, 
  intro x,
  show _ = matrix_to_map a_1 x + matrix_to_map b_1 x,
  show matrix_to_map (a_1 + b_1) x = _,
  unfold matrix_to_map,
  funext,
  show _ = (finset.sum finset.univ (λ (K : fin a), x K * a_1 K i)) +
       ( finset.sum finset.univ (λ (K : fin a), x K * b_1 K i)), 
      
  rw[← finset.sum_add_distrib],
  congr,
  funext,
  have H1: x K * (a_1 + b_1) K i = x K * (a_1 K i + b_1 K i),
  refl,
  rw[H1],
  rw[mul_add],
  end
}

theorem comp_is_linear_map {R : Type} [ring R] {a b c : nat} (f : (@linear_map R (has_space R b)  (has_space R a) _ _ _)) (g : (@linear_map R (has_space R c)  (has_space R b) _ _ _)):
  @is_linear_map R _ _ _ _ _ (f.1 ∘ g.1):= 
{ add:= 
begin 
intros,
simp,
have H1: f.val (g.val (x) + g.val(y)) = f.val (g.val (x + y)) ,
rw[g.2.add],
rw[← H1],
rw[f.2.add],
end,
smul:= 
begin 
intros,
simp,
have H1: f.val (g.val (c_1 • x)) = f.val(c_1 • g.val(x)),
rw[g.2.smul],
rw[H1],
rw[f.2.smul],
end 
}

theorem comp_equal_product_one {R : Type} [ring R] {a b c : nat} 
  (f : (@linear_map R (has_space R b)  (has_space R a) _ _ _)) 
  (g : (@linear_map R (has_space R c)  (has_space R b) _ _ _)):
(@map_to_matrix R _ c a (⟨ f.1 ∘ g.1,  comp_is_linear_map f g⟩)) 
  = @matrix.mul _ _ b c a (@map_to_matrix R _ c b g ) (@map_to_matrix R _ b a f) :=
begin
  unfold map_to_matrix,
  unfold matrix.mul,
  funext,
  simp,
  conv
  begin
    to_lhs,
    rw [span (g.1 (e R c i))],
  end,
  rw [is_linear_map.sum f.2],
  rw [apply_function_to_sum ],
  congr,
  funext,
  show  f.1 ((g.1 (e R c i) K) • (e R b K)) j = _,
  rw [is_linear_map.smul f.2],
  refl,
end

#check subtype
#check matrix.mul
theorem comp_equal_product_two {R : Type} [ring R] {a b c : nat} 
(M : matrix R b a) (N : matrix R c b):
@matrix_to_linear_map _ _ _ _ (@matrix.mul _ _ b c a N M) = 
⟨(@matrix_to_linear_map _ _ _ _ M).1 ∘ (@matrix_to_linear_map _ _ _ _ N).1, 
comp_is_linear_map (@matrix_to_linear_map _ _ _ _ M) (@matrix_to_linear_map _ _ _ _ N)⟩ :=
begin
  unfold matrix_to_linear_map,
  funext,
  apply subtype.eq,
  simp,
  unfold matrix_to_map,
  unfold matrix.mul,
  funext,
  simp,
  conv in (v _ * finset.sum _ _)
  begin 
  rw [finset.mul_sum],
  end,
  simp only [ finset.sum_mul],
  conv
  begin
    to_lhs,
    rw [finset.sum_comm],
  end,
  congr,
  funext,
  congr,
  funext,
  rw [mul_assoc],
  end

-- R-module structure on Hom(R^b, R^a)  

-- namespace vector_space
-- universes u v 
-- instance keji  {R : Type} [ring R] {a b : nat}:  is_add_group_hom (@map_to_matrix R _ a b):=
-- {
--   sorry
-- }

--   show (finset.sum finset.univ (λ (K : fin a), (a_1 K + b_1 K)  * M K i) =_),
-- conv in ( (a_1 _ + b_1 _) * M _ i)
--   begin
--     rw [add_mul],
--   end,
end map_matrix