import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import data.real.basic tactic.norm_num
import data.set.basic

universe u

open set filter lattice classical

noncomputable theory 


-- Useful continuity results for functions ℝ → ℝ

theorem real.continuous_add_const (r : ℝ) : continuous (λ x : ℝ, x + r) :=
begin
  have H₁ : continuous (λ x, (x,r) : ℝ → ℝ × ℝ),
    exact continuous.prod_mk continuous_id continuous_const,
  exact continuous.comp H₁ continuous_add', 
end 

theorem real.continuous_sub_const (r : ℝ) : continuous (λ x : ℝ, x - r) := 
continuous_sub continuous_id continuous_const 


theorem real.continuous_mul_const (r : ℝ) : continuous (λ x : ℝ, r*x) :=
begin 
    have H₁ : continuous (λ x, (r,x) : ℝ → ℝ × ℝ),
        exact continuous.prod_mk continuous_const continuous_id,
    show continuous ( (λ p : ℝ × ℝ , p.1 * p.2)  ∘  (λ (x : ℝ), (r,x))), 
    refine continuous.comp H₁  continuous_mul' , 
end 

theorem real.continuous_mul_const_right (r : ℝ) : continuous (λ x : ℝ, x*r) :=
begin 
    have H₁ : continuous (λ x, (x,r) : ℝ → ℝ × ℝ),
        exact continuous.prod_mk continuous_id continuous_const,
    refine continuous.comp H₁ continuous_mul' , 
end


theorem real.continuous_div_const (r : ℝ) : continuous (λ x : ℝ, x / r) :=
begin
  conv in (_ / r) begin
    rw div_eq_mul_inv,
  end,
  have H₁ : continuous (λ x, (x,r⁻¹) : ℝ → ℝ × ℝ),
    exact continuous.prod_mk continuous_id continuous_const,
  exact continuous.comp H₁ continuous_mul', 
end 


theorem real.continuous_scale (a b : ℝ) : continuous (λ x : ℝ, (x + a) / b) := 
continuous.comp (real.continuous_add_const a) (real.continuous_div_const b)


theorem real.continuous_linear (m q : ℝ) : continuous (λ x : ℝ, m * x + q) :=
begin 
    exact continuous.comp (real.continuous_mul_const m) (real.continuous_add_const q), 
end


--- Definition of closed intervals in ℝ 

def int_clos { r s : ℝ } ( Hrs : r < s ) : set ℝ := {x : ℝ  | r ≤ x ∧ x ≤ s}


theorem is_closed_int_clos { r s : ℝ } ( Hrs : r < s ) : is_closed (int_clos Hrs) := 
begin 
let L := {x : ℝ | x ≤ s} , 
let R := {x : ℝ | r ≤ x} , 
have C1 : is_closed L, exact is_closed_le' s, 
have C2 : is_closed R, exact is_closed_ge' r, 
have Int : int_clos Hrs =  R ∩ L, 
    unfold has_inter.inter set.inter , unfold int_clos, simp,  
rw Int, exact is_closed_inter C2 C1, 
end 
