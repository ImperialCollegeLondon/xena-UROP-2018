structure vector (R : Type) :=
vec :: (x : R) (y : R) (z : R)

namespace vector

variables {R : Type} [comm_ring R]

def zero : vector R := vec 0 0 0

def add (a b : vector R) := 
vec (a.x + b.x) (a.y + b.y) (a.z + b.z)

def neg (a : vector R) := 
vec (-a.x) (-a.y) (-a.z)

def cross_prod (a b : vector R) := 
vec (a.y * b.z - a.z * b.y) (a.x * b.z - a.z * b.x) (a.x * b.y - a.y * b.x)

def inner_prod (a b : vector R) := 
a.x * b.x + a.y * b.y +a.z * b.z

def scalar (n : R) (a : vector R) := 
vec (n * a.x) (n * a.y) (n * a.z)

theorem vector.ext (α : Type) (a b c d e f : α) :
a = d → b = e → c = f → vec a b c = vec d e f :=
begin
  intro Had, intro Hbe, intro Hcf,
  rw [Had,Hbe,Hcf]
end

theorem vector.add_comm :
 ∀ (a b : vector R) , 
 add a b = add b a :=
begin
  intro a , intro b ,
  unfold add,
  simp
end

theorem vector.add_asso : 
 ∀ (a b c : vector R) , 
 add a (add b c) = add (add a b) c :=
begin
  intro a , intro b , intro c ,
  unfold add,
  simp
end

theorem vector.inner_prod_comm :
 ∀ (a b : vector R) , 
 inner_prod a b = inner_prod b a :=
begin
  intro a ,
  intro b ,
  unfold inner_prod,
  rw [mul_comm, add_assoc, add_comm],
  rw [mul_comm, add_assoc, add_comm],
  rw mul_comm, simp
end

theorem vector.zero_zero : 
 ∀ (a : vector R) , 
 add zero a = add a zero :=
begin
  intro a,
  unfold add, unfold zero,
  simp,
end

theorem vector.zero_add : 
 ∀ (a : vector R) , 
 add zero a = a :=
begin
  intro a,
  unfold add, unfold zero,
  cases a with a.x a.y a.z,
  dsimp, congr,
  rw zero_add, rw zero_add, rw zero_add
end

theorem vector.add_zero : 
 ∀ (a : vector R) , 
 add a zero = a :=
begin
  intro a,
  unfold add, unfold zero,
  cases a with a.x a.y a.z,
  dsimp, simp
end

theorem vector.vec_assoc : 
 ∀ (a b : vector R) (n : R) , 
 scalar n (add a b) = add (scalar n a) (scalar n b) :=
begin
  intro a, intro b, intro n,
  unfold add, unfold scalar,
  dsimp, congr,
  rw mul_add, rw mul_add, rw mul_add
end

theorem vector.num_assoc : 
 ∀ (a : vector R) (m n : R) , 
 scalar (m + n) a = add (scalar m a) (scalar n a) :=
begin
  intro a, intro m, intro n,
  unfold add, unfold scalar,
  dsimp, congr,
  rw add_mul, rw add_mul, rw add_mul
end

theorem vector.cross_pord_comm : 
 ∀ (a b : vector R) , 
 neg (cross_prod b a) = cross_prod a b :=
begin
  intro a, intro b,
  unfold neg, unfold cross_prod,
  dsimp, congr, simp, 
  rw [mul_comm, add_comm, mul_comm], simp, 
  rw [mul_comm, add_comm, mul_comm], simp, 
  rw [mul_comm, add_comm, mul_comm], simp, 
end

theorem mul_comm1 : 
 ∀ (a b c : R) , 
 a * b * c = c * a * b :=
begin
 intro a, intro b, intro c,
 rw [mul_comm, ← mul_assoc]
end

theorem mul_comm2 : 
 ∀ (a b c : R) , 
 a * b * c = b * c *a :=
begin
 intro a, intro b, intro c,
 rw [mul_assoc, mul_comm]
end

theorem Jacobian_Identity :
  ∀ (a b c : vector R) , 
 add (cross_prod a (cross_prod b c)) (add (cross_prod b (cross_prod c a)) (cross_prod c (cross_prod a b))) = zero :=
begin
  intro a, intro b, intro c,
  unfold add, unfold cross_prod, unfold zero,
  dsimp, congr,
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add], 
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw [mul_comm1, add_comm, add_assoc],
  rw [mul_comm1, add_comm, add_assoc, add_assoc],
  rw [mul_comm1, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc],
  rw [mul_comm, add_comm], simp,
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add], 
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw [mul_comm2, add_comm, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc],
  rw [mul_comm, add_comm], simp,
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add], 
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw mul_comm, simp, rw mul_comm, simp, rw mul_comm, simp,
  rw [mul_comm2, add_comm, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm2, add_comm, add_assoc, add_assoc],
  rw [mul_comm1, add_comm, add_assoc, add_assoc],
  rw [mul_comm1, add_comm, add_assoc, add_assoc],
  rw [mul_comm1, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc, add_assoc],
  rw [mul_comm, add_comm, add_assoc],
  rw [mul_comm, add_comm], simp,
end

end vector