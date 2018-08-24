/-
Copyright (c) 2018 Luca Gerolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luca Gerolla, Kevin Buzzard
Prove basic results of real continuous functions and closed intervals
-/
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
  continuous.comp (real.continuous_mul_const m) (real.continuous_add_const q)



--- Definition of closed intervals in ℝ 
                                                                                                 
def int_clos { r s : ℝ } ( Hrs : r < s ) : set ℝ := {x : ℝ  | r ≤ x ∧ x ≤ s}


theorem is_closed_int_clos { r s : ℝ } ( Hrs : r < s ) : is_closed (int_clos Hrs) := 
  is_closed_inter (is_closed_ge' r) (is_closed_le' s) 

