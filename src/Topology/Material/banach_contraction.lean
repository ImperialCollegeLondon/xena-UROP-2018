import analysis.topology.topological_space
import analysis.topology.continuity
import tactic.norm_num
import analysis.metric_space
import analysis.topology.uniform_space
import order.filter
import analysis.limits

import Topology.Material.topological_sequences

--Start of Chris's Stuff
import data.complex.basic algebra.archimedean data.nat.binomial algebra.field_power tactic.linarith

section
open real is_absolute_value finset

local attribute [instance, priority 0] classical.prop_decidable

lemma geo_sum_eq {α : Type*} [field α] {x : α} : ∀ (n : ℕ) (hx1 : x ≠ 1),
  (range n).sum (λ m, x ^ m) = (1 - x ^ n) / (1 - x)
| 0     hx1 := by simp
| (n+1) hx1 := have 1 - x ≠ 0 := mt sub_eq_zero_iff_eq.1 hx1.symm,
by rw [sum_range_succ, ← mul_div_cancel (x ^ n) this, geo_sum_eq n hx1, ← add_div, _root_.pow_succ];
    simp [mul_add, add_mul, mul_comm]
end
--End of Chris's stuff


local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

def discrete_metric_space' (α : Type*) : metric_space α :=
{
    dist := λ a b, if a = b then 0 else 1,
    dist_self := begin intro x, unfold ite,
        rw eq_true_intro (eq.refl x), exact if_true 0 1,
        end,
    eq_of_dist_eq_zero := begin intros x y, dsimp, split_ifs,
      intro _,exact h,
      norm_num,
        end,
    dist_comm := begin intros x y, dsimp,
      split_ifs,
        refl,
        cases (h_1 h.symm),
        cases (h h_1.symm),
        refl
        end,
    dist_triangle := begin
      intros, dsimp, split_ifs,
        right,refl,
        left,show (0 : ℝ) < 0 + 1,norm_num,
        left,show (0 : ℝ) < 1 + 0,norm_num,
        left,show (0 : ℝ) < 1 + 1,norm_num,
        exfalso,apply h,rwa h_1,
        right,refl,
        right,refl,
        left, show (1 : ℝ) < 1 + 1, norm_num,
    end
}

open function

--Half of Proposition 17.4
theorem complete_of_complete_of_uniform_cts_bij {α : Type*} [metric_space α] {β : Type*} [metric_space β] (f : α → β)
    (g : β → α) (Hf : uniform_continuous f) (Hg : uniform_continuous g) (left_inv : function.left_inverse g f)
    (right_inv : function.right_inverse g f) : complete_space α → complete_space β :=
begin
  rintro ⟨H1⟩,
  split,
  intros filt Hfilt,

  cases H1 (cauchy_map Hg Hfilt) with x H_converges_to_x,
  existsi f x,
  rw [filter.map_le_iff_le_vmap,
      ←filter.map_eq_vmap_of_inverse (id_of_right_inverse right_inv) (id_of_left_inverse left_inv)] at H_converges_to_x,

  exact le_trans H_converges_to_x (continuous.tendsto Hf.continuous x)
end







--Proposition 17.4
theorem complete_iff_of_uniform_cts_bij {α : Type*} [metric_space α] {β : Type*} [metric_space β] (f : α → β) 
    (g : β → α) (Hf : uniform_continuous f) (Hg : uniform_continuous g) (left_inv : function.left_inverse g f)
    (right_inv : function.right_inverse g f) : complete_space α ↔ complete_space β := 
begin
  exact ⟨complete_of_complete_of_uniform_cts_bij f g Hf Hg left_inv right_inv,
        complete_of_complete_of_uniform_cts_bij g f Hg Hf right_inv left_inv⟩,
end

open nat
def iteration_map {α : Type*} (f : α → α) (start : α) : ℕ → α
| zero := start
| (succ x) := f (iteration_map x)

#print prefix iteration_map

--Definition 17.24
def is_contraction {α : Type*} [metric_space α] (f : α → α) := 
∃ (k : ℝ) (H1 : k < 1) (H2 : 0 < k), ∀ (x y : α), dist (f x) (f y) ≤ k* (dist x y)

--Lemma 17.25


set_option pp.all false
--Banach's fixed point theorem
theorem Banach_fixed_point {α : Type*} [metric_space α] [complete_space α] (H1 : nonempty α) {f : α → α} (H : is_contraction f)
: ∃! (p : α), f p = p :=
begin
  cases classical.exists_true_of_nonempty H1 with start trivial,
  let seq := iteration_map f start,
  rcases H with ⟨K, HK1, HK2, Hf⟩,
--My zero is his one
  have consecutive_distance : ∀ n, dist (seq (n+1)) (seq (n)) ≤ K^n * dist (seq 1) (seq 0),
    intro n, induction n with N HN,
      show dist (seq 1) (seq 0) ≤ 1 * dist (seq 1) (seq 0),
      rw one_mul,
    have K_times_HN := (mul_le_mul_left HK2).2 HN,
    rw ← mul_assoc at K_times_HN,
    exact le_trans (Hf (seq (N+1)) (seq (N+0))) K_times_HN,
    
    --Now repeatedly use the triangle inequality
    let sum_consecutives := λ m n, finset.sum (finset.range (m)) (λ x, dist (seq (n+x+1)) (seq (n+x))), 
    have le_sum_consecutives : ∀ m n, dist (seq (n+m)) (seq n) ≤ sum_consecutives m n,
      intros m n,
      induction m with M HM,
        rw add_zero, rw dist_self,
        apply finset.zero_le_sum,
        intros n Hn, exact dist_nonneg,
      have sum_cons_insert : sum_consecutives (succ M) n = 
        finset.sum (insert (M) (finset.range (M))) (λ (x : ℕ), dist (seq (n + x + 1)) (seq (n + x))),
        have : (finset.range (succ M)) = insert M (finset.range M),
          rw finset.range_succ,
        dsimp [sum_consecutives],
        rw this,
      have dist_triangleone : dist (seq (n + succ M)) (seq n) ≤ 
          dist (seq (n + succ M)) (seq (n+M)) + dist (seq (n + M)) (seq n),
        exact dist_triangle _ _ _,
      refine le_trans dist_triangleone _,
      rw sum_cons_insert,
      rw finset.sum_insert (by rw finset.mem_range; exact lt_irrefl M),
      apply add_le_add_left, exact HM,

    let sum_consecutives_K := λ m n, finset.sum (finset.range (m)) (λ x,(K^(n+x))*dist (seq 1) (seq 0)),

    have sum_le : ∀ m n, sum_consecutives m n ≤ sum_consecutives_K m n,
      intros m n, apply finset.sum_le_sum,
      intros x Hx, exact consecutive_distance (n+x),
    
    
    have take_out_dist : ∀ m n, sum_consecutives_K m n = 
        (finset.sum (finset.range m) (λ (x : ℕ), K ^ (x)))* (K^n)*dist (seq 1) (seq 0),
      intros m n, rw finset.sum_mul, rw finset.sum_mul,
      simp only [(_root_.pow_add _ _ _).symm, add_comm],
    


    replace take_out_dist : ∀ (m n : ℕ), sum_consecutives_K m n = (1 - K ^ m) / (1 - K) * K ^ n * dist (seq 1) (seq 0),
      intros m n,
      rw [← geo_sum_eq _ (ne_of_lt HK1), take_out_dist m n],
    
    have : ∀ (m : ℕ), (1 - K ^ m) ≤ 1,
      intros m, refine sub_le_self 1 ((pow_nonneg (le_of_lt HK2)) m),

    have this2 : ∀ (n : ℕ), 0 ≤ (1 - K)⁻¹ * (K ^ n * dist (seq 1) (seq 0)),
      intro n, rw ← mul_assoc, refine mul_nonneg (mul_nonneg (le_of_lt (inv_pos'.2 (by linarith))) (le_of_lt ((pow_pos HK2) n))) dist_nonneg,

    have k_sum_le_k_sum : ∀ (m n : ℕ), (1 - K ^ m) / (1 - K) * K ^ n * dist (seq 1) (seq 0) 
        ≤ 1 / (1 - K) *(K ^ n)* dist (seq 1) (seq 0),
      intros m n, rw [mul_assoc, mul_assoc, div_eq_mul_inv, mul_assoc, div_eq_mul_inv, mul_assoc],
      refine mul_le_mul_of_nonneg_right (this m) (this2 n),

    have k_to_n_converges := tendsto_pow_at_top_nhds_0_of_lt_1 (le_of_lt HK2) HK1,
    have const_converges : filter.tendsto (λ (n : ℕ), 1 / (1 - K) * dist (seq 1) (seq 0)) filter.at_top (nhds (1 / (1 - K) * dist (seq 1) (seq 0))),
      exact tendsto_const_nhds,
    

    have k_sum_converges := tendsto_mul k_to_n_converges const_converges, dsimp at k_sum_converges,
      rw zero_mul at k_sum_converges,

    have equal : ∀ (n : ℕ), K ^ n * (1 / (1 + -K) * dist (seq 1) (seq 0)) =  1 / (1 - K) * K ^ n * dist (seq 1) (seq 0),
      intro n, conv in (_ * K ^ n) begin rw mul_comm, end, rw mul_assoc, refl,
    
    rw seq_tendsto_iff at k_sum_converges, 

    have cauchy_seq : ∀ ε > 0, ∃ (N : ℕ), ∀ {n m}, n ≥ N → m ≥ N → dist (seq n) (seq m) < ε,
      intros ε Hε,
      cases k_sum_converges ε Hε with N HN,
      existsi N,
      intros r s Hr Hs,
      wlog h : s ≤ r,
      --Something about r > s
      have := HN Hs,
      rw real.dist_eq at this, rw sub_zero at this,
      replace := (abs_lt.1 this).2, rw equal at this,
      have this2 := λ m, lt_of_le_of_lt (k_sum_le_k_sum m s) this,
      have this3 : ∀ (m : ℕ), sum_consecutives_K m s < ε,
        intro m, rw take_out_dist, exact this2 m,
      have this4 := λ m, lt_of_le_of_lt (sum_le m s) (this3 m),
      have this5 := λ m, lt_of_le_of_lt (le_sum_consecutives m s) (this4 m),
      cases le_iff_exists_add.1 h with c Hc,
      rw Hc,
      exact this5 c,
    rw dist_comm,
    exact this_1 Hs Hr,
    
  rw ← metric_space.seq_cauchy_of_mathematician at cauchy_seq,

  cases @complete_space.complete _ _ _inst_2 _ cauchy_seq with p Hp,

  existsi p,
  have f_p_is_p : f p = p, 
   

  sorry,
  split,
    exact f_p_is_p,

  intros y Hy,
  by_contra H,
  have H4 := @dist_nonneg _ _ p y,

  have H3 : 0 < dist p y, exact or.elim H4 (λ x, x) (λ m, by_contradiction 
    (λ o, H (eq_of_dist_eq_zero (eq.symm (eq.trans m (dist_comm p y)))))),

  have := Hf p y, rw [Hy, f_p_is_p] at this,
  have this1_5 : K * dist p y < 1 * dist p y,
    apply lt_of_sub_pos, rw ← mul_sub_right_distrib, refine mul_pos (sub_pos_of_lt HK1) H3,

  have this2 : dist p y < 1 * dist p y,
    refine lt_of_le_of_lt this this1_5, rw one_mul at this2, apply lt_irrefl (dist p y) this2,
  
end
#print prefix Banach_fixed_point
#print tendsto_of_tendsto_of_tendsto_of_le_of_le
#print prefix canonically_ordered_comm_semiring
#print by_contradiction

#print tendsto_map
--Lemma 17.25, applying continuous function applied to sequence 
--tending to limit, seq(succ n) tendsto same,

--

-- limits section is good

