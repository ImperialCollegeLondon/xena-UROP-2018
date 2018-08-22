-- copyright 2017/18 Ellen Arlt
-- August 2018, Proved module R (matrix R n m) by Blair Shi

import algebra.big_operators data.set.finite
import algebra.module 

definition matrix (R: Type) (n m : nat)[ring R] :=  fin n →( fin m → R ) 
 
namespace matrix 

definition add ( R : Type) [ring R] {n m: nat }(A:matrix R m n) ( B : matrix R m n): (matrix R m n):= 
λ I J, A I J + B I J

definition neg ( R : Type) [ring R] {n m: nat } (A:matrix R m n) : (matrix R m n):= 
λ I J, - A I J

definition zero ( R : Type) [ring R] {m n: nat }: (matrix R m n):= 
λ  I J , 0 

definition sub ( R : Type) [ring R] {n m: nat }(A:matrix R m n) ( B : matrix R m n): (matrix R m n):=
λ I J, A I J - B I J

theorem add_assoc1 ( R : Type) [ring R] {m n: nat }(A:matrix R m n) ( B : matrix R m n) ( C : matrix R m n) :
 add R A (add R  B C) = add R (add R A B) C :=
begin
apply funext,
intro,
apply funext,
intro y,
unfold add,
show A x y + (B x y + C x y) = ( A x y + B x y) + C x y,
rw [add_assoc],
end

theorem add_assoc2 ( R : Type) [ring R] {m n: nat }(A:matrix R m n) ( B : matrix R m n) ( C : matrix R m n) :
 add R (add R A B) C = add R A (add R  B C)  :=
begin
apply funext,
intro,
apply funext,
intro y,
show  ( A x y + B x y) + C x y = A x y + (B x y + C x y) ,
rw[add_assoc],
end

theorem zero_add   ( R : Type) [ring R] {m n: nat }(A:matrix R m n):
add R (zero R) A = A:=
begin
apply funext,
intro,
apply funext,
intro y,
show 0 + A x y = A x y,
rw[zero_add]
end

theorem add_zero (R : Type) [ring R] {m n: nat }(A:matrix R m n):
add R A (zero R) = A:=
begin
apply funext,
intro,
apply funext,
intro y,
show  A x y + 0 = A x y,
rw[add_zero]
end


theorem add_left_neg (R : Type) [ring R] {m n: nat }(A:matrix R m n) :
add R ( neg R A) A = zero R := 
begin
apply funext,
intro,
apply funext,
intro y,
show  - A x y + A x y = 0 ,
rw[add_left_neg]
end


theorem add_comm (R : Type) [ring R] {m n: nat }(A:matrix R m n)( B : matrix R m n):
add R A B = add R B A :=
begin
apply funext,
intro,
apply funext,
intro y,
show  A x y + B x y = B x y + A x y ,
rw [add_comm]
end


instance matrices_add_comm_group ( R : Type) [ring R] {m n: nat }: add_comm_group (matrix R m n):={
add:= matrix.add R ,
add_assoc := @matrix.add_assoc2 R _ m n,
zero := matrix.zero R ,
neg := matrix.neg R,
zero_add := @matrix.zero_add R _ m n,
add_zero := @matrix.add_zero R _ m n,
add_left_neg := @matrix.add_left_neg R _ m n,
add_comm := @matrix.add_comm R _ m n
}

definition mul ( R : Type) [ring R] {n m l: nat }(A:matrix R m n) ( B : matrix R n l): (matrix R m l ):= 
λ I J, finset.sum finset.univ (λ K, A I K * B K J) 
 
theorem mul_assoc ( R : Type) [ring R] {m n l o: nat }(A:matrix R m n) ( B : matrix R n l) ( C : matrix R l o) :
mul R A (mul R B C) = mul R (mul R A B) C :=
begin
unfold mul,
apply funext,
intro x,
apply funext,
intro y,
-- This next line just rewrites the goal so that the variables we're summing over 
-- are the same on both sides.

show finset.sum finset.univ (λ (K : fin n), A x K * finset.sum finset.univ (λ (J : fin l), B K J * C J y)) =
     finset.sum finset.univ (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J) * C J y),
-- So the key things we now need to use are:

-- finset.mul_sum (which says c * sum_n a_n = sum_n (c*a_n))
-- finset.sum_mul (which says the same but multiplication on the right)
-- and finset.sum_comm (which says that two finite sums can be commuted).

-- However, rw finset.sum_mul doesn't work
-- and neither does rw finset.mul_sum,
-- and until we apply these we can't commute the sums.
-- I think the reasons they don't work are that C J y, which we need to move, depends on J,
-- which is not one of our variables.

-- So here's a trick. We prove an intermediate lemma which says we can
-- move C J y into the sum, by checking the things we're summing over are the same.

have H2 : (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J) * C J y)
        = (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J * C J y)),
{ apply funext,
  intro J,
  exact finset.sum_mul,
},

-- Now we can commute the sums after using this lemma.

rw [H2],
clear H2,
rw [finset.sum_comm],

-- Now I just rewrite the goal to show that both things are a sum over K in fin n.

show finset.sum finset.univ (λ (K : fin n), A x K * finset.sum finset.univ (λ (K_1 : fin l), B K K_1 * C K_1 y)) =
    finset.sum finset.univ (λ (K : fin n), finset.sum finset.univ (λ (x_1 : fin l), A x K * B K x_1 * C x_1 y)),

-- Now we can cancel the first sum and it's all downhill from here.

apply congr_arg _,
apply funext,
intro z,
rw finset.mul_sum, -- c*sum a_n = sum c*a_n

apply congr_arg,
apply funext,

intro w,
rw mul_assoc,
end

theorem left_distrib (R:Type) [ring R] {m n l  : nat} (A : matrix R m n) (B : matrix R n l) (C : matrix R n l ) :
mul R A (add R B C) = add R (mul R A B) (mul R A C) :=
begin
unfold mul,
unfold add,
apply funext,
intro x,
apply funext,
intro y,


have H3 :     finset.sum finset.univ (λ (K : fin n), A x K * B K y) + finset.sum finset.univ (λ (K : fin n), A x K * C K y)
            = finset.sum finset.univ (λ (K : fin n), A x K * B K y + A x K * C K y),
{simp[finset.sum_add_distrib]},

rw[H3],
clear H3,

apply congr_arg _,
apply funext,
intro z,
rw [left_distrib]
end


theorem right_distrib (R:Type) [ring R] {m n l  : nat} (A : matrix R m n) (B : matrix R m n) (C : matrix R n l ) :
mul R (add R A B) C  = add R (mul R A C) (mul R B C) :=
begin
unfold mul,
unfold add,
apply funext,
intro x,
apply funext,
intro y,

have H4 :     finset.sum finset.univ (λ (K : fin n), A x K * C K y) + finset.sum finset.univ (λ (K : fin n), B x K * C K y)
            = finset.sum finset.univ (λ (K : fin n), A x K * C K y + B x K * C K y),
{simp[finset.sum_add_distrib]},

rw[H4],
clear H4,

apply congr_arg _,
apply funext,
intro z,
rw [right_distrib]
end

theorem mul_sub_mul {R : Type} [comm_ring R] (a b c : ℕ) :
∀ (A B: matrix R a b), ∀ C : matrix R b c,
matrix.sub R (matrix.mul R A C) (matrix.mul R B C) = matrix.mul R (matrix.sub R A B) C :=
begin 
intros A B C,
unfold matrix.sub,
unfold matrix.mul,
funext,
conv in ((A _ _ - B _ _) * C _ _)
begin
  rw [sub_mul],
end,
{simp[finset.sum_add_distrib]},
end

definition identity_matrix ( R : Type) [ring R] { n: nat }: (matrix R n n):= 
λ  I J ,
if I=J then 1
else 0

--set_option pp.all true
--set_option pp.notation false
theorem one_mul ( R : Type) [ring R] {n: nat }(A:matrix R n n):
mul R (identity_matrix R) A = A:=
begin
unfold mul,
unfold identity_matrix,
apply funext,
intro x,
apply funext,
intro y,
let xfinset : finset (fin n) := finset.singleton x,
suffices : finset.sum finset.univ (λ (K : fin n), ite (x = K) 1 0 * A K y)
            = finset.sum xfinset (λ t, A t y),
  simp [this],
--  exact finset.sum_singleton,
  apply eq.symm,
  have H1 : finset.sum xfinset (λ (t : fin n), A t y) = finset.sum xfinset (λ (K : fin n), ite (x = K) 1 0 * A K y),
    rw finset.sum_singleton, 
    rw finset.sum_singleton, 
    simp,
  rw H1,
  refine (finset.sum_subset (_ : xfinset ⊆ finset.univ) _),
  exact finset.subset_univ xfinset,
  intros K H H2,
  have H3 : ¬ (x = K),
    intro H4,
    apply H2,
    rw ←H4,
    apply finset.mem_singleton.2,
    refl,
  simp [H3],  

end
--#check @finset.sum_subset
--finset.sum_subset :
--  ∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : finset α} {f : α → β} [_inst_1 : add_comm_monoid β],
--    s₁ ⊆ s₂ → (∀ (x : α), x ∈ s₂ → x ∉ s₁ → f x = 0) → finset.sum s₁ f = finset.sum s₂ f

theorem mul_one ( R : Type) [ring R] {n: nat }(A:matrix R n n):
mul R A (identity_matrix R) = A:=
begin
unfold mul,
unfold identity_matrix,
apply funext,
intro x,
apply funext,
intro y,
let yfinset : finset (fin n) := finset.singleton y,
suffices : finset.sum finset.univ (λ (K : fin n), A x K * ite (K = y) 1 0 )
           = finset.sum yfinset (λ t, A x t),  
simp [this],
apply eq.symm,
have H1 : finset.sum yfinset (λ (t : fin n), A x t) = finset.sum yfinset (λ (K : fin n), A x K * ite (K = y) 1 0 ),
         rw finset.sum_singleton, 
         rw finset.sum_singleton, 
         simp,
rw H1,
refine (finset.sum_subset (_ : yfinset ⊆ finset.univ) _),
exact finset.subset_univ yfinset,
intros K H H2,
have H3 : ¬ (K = y),
         intro H4,
         apply H2,
         rw H4,
         apply finset.mem_singleton.2,
         refl,
simp[H3],
end


instance ring ( R : Type) [ring R] { n: nat }: ring (matrix R n n):={
add:= matrix.add R ,
add_assoc := @matrix.add_assoc2 R _ n n,
zero := matrix.zero R ,
neg := matrix.neg R,
zero_add := @matrix.zero_add R _ n n,
add_zero := @matrix.add_zero R _ n n,
add_left_neg := @matrix.add_left_neg R _ n n,
add_comm := @matrix.add_comm R _ n n,
mul := matrix.mul R,
mul_assoc := λ A B C, eq.symm $ @matrix.mul_assoc R _ n n n n A B C,
mul_one := @matrix.mul_one R _ n ,
one := matrix.identity_matrix R,
one_mul := @matrix.one_mul R _ n ,
left_distrib := @matrix.left_distrib R _ n n n,
right_distrib := @matrix.right_distrib R _ n n n
}

end matrix

namespace M_module

def smul_M {F : Type} {n m : ℕ} [ring F] (a : F) (M : matrix F n m) :
matrix F n m := λ I, λ J, a * (M I J)

instance (F : Type) [ring F] (n m : ℕ) : has_scalar F (matrix F n m) :=
{ 
    smul := smul_M
}

theorem smul_add' {F : Type} {n m : ℕ} [ring F] (s : F) (m1 m2 : matrix F n m) : 
  smul_M s (matrix.add F m1 m2) = matrix.add F (smul_M s m1) (smul_M s m2) := 
begin
unfold smul_M,
funext,
unfold matrix.add,
rw [mul_add],
end

theorem add_smul' {F : Type} {n m : ℕ} [ring F] (s t : F) (M : matrix F n m) :
smul_M (s + t) M = (smul_M s M) + (smul_M t M) := 
begin
unfold smul_M,
simp only [add_mul],
funext,
congr,
end

theorem mul_smul' {F : Type} {n m : ℕ} [ring F] (s t : F) (M : matrix F n m) :
smul_M (s * t) M = smul_M s (smul_M t M) := 
begin
unfold smul_M,
funext,
rw [mul_assoc],
end

theorem one_smul' {F : Type} {n m : ℕ} [ring F] (M : matrix F n m) :
smul_M (1 : F) M = M :=
begin
  unfold smul_M,
  funext,
  rw [one_mul],
end

instance {R : Type} {n m : ℕ} [ring R] : module R (matrix R n m) :=
{
  smul_add := smul_add',
  add_smul := add_smul',
  mul_smul := mul_smul',
  one_smul := one_smul',
}
end M_module
/-

dec_trivial
finset.range
I.val 
-/
