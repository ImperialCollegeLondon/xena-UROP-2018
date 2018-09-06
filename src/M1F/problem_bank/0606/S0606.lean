import analysis.real tactic.norm_num algebra.group_power

def S (a : {n : ℕ // n ≥ 1} → ℝ) 
  (n : ℕ) (H : n ≥ 1) := { r: ℝ | ∃ (m : ℕ) (Hm : m ≥ n), r = a ⟨m,ge_trans Hm H⟩ }

/- HORRIBLE ERROR 
theorem Q6a1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) : ∀ (n : ℕ) (H : n ≥ 1), 
  (∃ r : ℝ, r ∈ S a HB n H) ∧ (∃ B : ℝ, ∀ x : ℝ, x ∈ S a HB n H → x ≤ B) :=
begin
intros n Hn,
split,
{ existsi a ⟨n Hn⟩,
}
end
-/

--set_option trace.class_instances true

theorem Q6a1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) : ∀ (n : ℕ) (H : n ≥ 1), 
  (∃ r : ℝ, r ∈ S a n H) ∧ (∃ B : ℝ, ∀ x : ℝ, x ∈ S a n H → x ≤ B) :=
begin
intros n Hn,
split,
{ existsi a ⟨n,Hn⟩,
  existsi n,
  existsi (le_of_eq (refl n)),
  refl },
cases HB with B H,
existsi B,
intro x,
intro Hx,
cases Hx with m Hm,
cases Hm with H1 Hx,
rw Hx,
refine H _ _,
end

theorem Q6a2 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) : 
  ∃ x : ℝ, is_lub (S a n H) x :=
begin
have H1 := Q6a1 a HB n H,
cases H1.left with y Hy,
cases H1.right with B H2,
refine exists_supremum_real Hy H2
end 

theorem Q6b1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) :
  ∀ bnp1 bn : ℝ, is_lub (S a n H) bn ∧ is_lub (S a (n+1) (le_trans H (nat.le_succ _))) bnp1
  → bnp1 ≤ bn :=
begin
introv H1,
suffices : bn ∈ upper_bounds (S a (n+1) (le_trans H (nat.le_succ _))),
refine (H1.right).right bn this,
intros x Hx,
suffices : x ∈ (S a n H),
exact H1.left.left x this,
cases Hx with m Hm,
cases Hm with H2 H3,
existsi m,
existsi (le_trans (nat.le_succ _) H2),
assumption
end 

def limsup (a : {n : ℕ // n ≥ 1} → ℝ) (lsup : ℝ) : Prop :=
  ∃ b : { n : ℕ // n ≥ 1} → ℝ, is_glb { x : ℝ | ∃ (n : ℕ) (H : n ≥ 1), x = b ⟨n,H⟩} lsup 
  ∧ ∀ (n : ℕ) (H : n ≥ 1), is_lub (S a n H) (b ⟨n,H⟩) 

def a1 : {n : ℕ // n ≥ 1} → ℝ := λ _, 1
theorem Q6c1 : limsup a1 1 :=
begin
existsi (λ _,(1:ℝ)),
split,
{ split,
  { intros y Hy,
    cases Hy with n Hn,
    cases Hn with H1 H2,
    rw H2,
    show (1:ℝ) ≤ 1,
    norm_num
  },
  intros y Hy,
  have H1 := Hy 1,
  refine H1 _,
  existsi 1,
  existsi (show 1 ≤ 1, by norm_num),
  simp

},
intros n Hn,
show is_lub (S a1 n Hn) 1,
split,
{ intros x Hx,
  cases Hx with m Hm,
  cases Hm with H1 H2,
  rw H2,
  show (1:ℝ)≤1,
  norm_num
},
{ intros x Hx,
  have H1 := Hx 1,
  apply H1,
  clear H1, -- ask Mario how to do apply then clear
  existsi n,
  existsi _,
  {refl},
  show n≤n,
  refl,


}
end

--set_option pp.all true

noncomputable def a2 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1/N.val 
theorem Q6c2 : limsup a2 0 :=
begin
existsi a2,
split,
{ split,
  { 
  intros x Hx,
  cases Hx with m Hm,
  cases Hm with H1 H2,
  rw H2,
  show (0:ℝ) ≤ 1/m,
  refine div_nonneg_of_nonneg_of_pos _ _,
  {norm_num},
  refine lt_of_lt_of_le zero_lt_one _,
  rwa [←nat.cast_one,nat.cast_le] },
  { intros y Hy,
    refine not_lt.1 _,
    intro Hny,
    cases (exists_lt_nat (1/y)) with m Hm,
    have H1 := Hy (1/m),
    rw ←inv_eq_one_div at Hm,
    have H2 : m ≥ 1,
    { have H3 : ↑0 < ↑m := lt_trans (inv_pos Hny) Hm,
      rw [nat.cast_lt] at H3,
      exact nat.succ_le_of_lt H3 },
    have H4 : 1 / (↑m:ℝ) ∈ {x : ℝ | ∃ (n : ℕ) (H : n ≥ 1), x = a2 ⟨n, H⟩},
    { existsi [m,H2],
      refl },
    have H5 := H1 H4,
    have H6 := inv_le_inv _ _ Hny H5,
    rw [←inv_eq_one_div,inv_inv'] at H6,
    apply lt_irrefl (m:ℝ),
    exact lt_of_le_of_lt H6 Hm,
  }
},
{
intros n H,
split,
{ intros x Hx,
  cases Hx with d Hd,
  cases Hd with Hm H1,
  rw H1,
  show 1/(d:ℝ) ≤ 1/n,
  rw [←inv_eq_one_div,←inv_eq_one_div],
  refine inv_le_inv _ _ _ _,
  { rw [←nat.cast_zero,nat.cast_lt], exact lt_of_lt_of_le zero_lt_one H},
  rwa [nat.cast_le]
  },
intros x Hx,
have := Hx (1/(n:ℝ)),
apply this,
existsi n,
existsi _,
refl,
show n ≤ n,
refl
}
end


noncomputable def a3 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1 - ((((N.val % (2:ℕ))):ℤ):ℝ)
--#eval a3 ⟨1,dec_trivial⟩

theorem Q6c3 : limsup a3 1 :=
begin
existsi (λ _, (1:ℝ)),
split,
{ split,
  { intros x Hx,
    cases Hx with m Hm,
    cases Hm with H1 H2,
    rw H2,
    simp [le_refl],
  },
  intros x Hx,
  apply Hx,
  existsi 2,
  existsi _,
  refl,
  exact dec_trivial,

},
intros n Hn,
split,
{ intros y Hy,
  cases Hy with m Hm,
  show y ≤ 1,
  cases Hm with H1 H2,
  rw H2,
  unfold a3,
  refine sub_le_self _ _,
  rw [←int.cast_zero],
  unfold ge,
  rw int.cast_le,
  refine int.mod_nonneg _ _,
  exact dec_trivial,
},
intros x Hx,
show 1 ≤ x,
apply Hx,
existsi (2*n),
existsi _,
{ unfold a3,
  simp,
},
rw [mul_comm,mul_two],
exact nat.le_add_left _ _,
end

/-
Say we have a sequence of real numbers a 1 , a 2 , a 3 , . . ., which is
 bounded above in the sense
that there exists some real number B such that a i ≤ B for all i.
Now let’s define some sets S 1 , S 2 , S 3 , . . . by
S n = {a n , a n+1 , a n+2 , . . .}.
For example S 3 = {a 3 , a 4 , a 5 , . . .}.
a) Prove that for all n ≥ 1, S n is a non-empty set which is bounded above, and hence has a
least upper bound b n .
b) Prove that b n+1 ≤ b n and hence b 1 , b 2 , b 3 is a decreasing sequence.
If the set {b 1 , b 2 , b 3 , . . .} is bounded below, then its greatest lower bound ` is called the limsup
of the sequence (a 1 , a 2 , a 3 , . . .) (this is an abbreviation for Limit Superior).
c) Find the limsup of the following sequences (they do exist).
i) 1, 1, 1, 1, 1, . . .
ii) 1, 2 1 , 13 , 14 , . . .
iii) 0, 1, 0, 1, 0, 1, 0, 1, . . .
d) If you like, then guess the definition of liminf (Limit Inferior) and compute it for examples
(i) to (iii) of (c) above. Which of these sequences converges? Can you tell just from looking at
the limsup and liminf?-/

def liminf (a : {n : ℕ // n ≥ 1} → ℝ) (linf : ℝ) : Prop :=
  ∃ c : { n : ℕ // n ≥ 1} → ℝ, is_lub { x : ℝ | ∃ (n : ℕ) (H : n ≥ 1), x = c ⟨n,H⟩} linf 
  ∧ ∀ (n : ℕ) (H : n ≥ 1), is_glb (S a n H) (c ⟨n,H⟩) 

theorem Q6c1' : liminf a1 1 :=
begin
existsi (λ _,(1:ℝ)),
split,
{ split,
  { intros y Hy,
    cases Hy with n Hn,
    cases Hn with H1 H2,
    rw H2,
    show (1:ℝ) ≤ 1,
    exact le_refl _,
  },
  intros y Hy,
  have H1 := Hy 1,
  refine H1 _,
  existsi 1,
  existsi (show 1 ≤ 1, by exact le_refl _),
  simp
},
intros n Hn,
show is_glb (S a1 n Hn) 1,
split,
{ intros x Hx,
  cases Hx with m Hm,
  cases Hm with H1 H2,
  rw H2,
  show (1:ℝ)≤1,
  exact le_refl _,
},
{ intros x Hx,
  have H1 := Hx 1,
  apply H1,
  clear H1, -- ask Mario how to do apply then clear
  existsi n,
  existsi _,
  {refl},
  show n≤n,
  refl,
}
end 

theorem Q6c2' : liminf a2 0 :=
begin
existsi (λ _,(0:ℝ)),
split,
{ split,
  { 
  intros x Hx,
  cases Hx with m Hm,
  cases Hm with H1 H2,
  rw H2,
  exact le_refl _,
  },
  intros y Hy,
  apply Hy,
  existsi 1,
  existsi _,refl,
  show 1 ≤ 1,
  exact le_refl _
},
intros n Hn,
split,
{ intros x Hx,
  cases Hx with m Hm,
  cases Hm with H1 H2,
  show 0 ≤ x,
  rw H2,
  unfold a2,
  show 0 ≤ 1/(↑m:ℝ),
  rw [←inv_eq_one_div],
  apply le_of_lt _,
  apply inv_pos,
  rw [←nat.cast_zero,nat.cast_lt],
  exact calc 0 < 1 : zero_lt_one ... ≤ n : Hn ... ≤ m : H1
},
intros x Hx,
show x ≤ 0,
    refine not_lt.1 _,
    intro Hny,
    cases (exists_lt_nat (max (1/x) n)) with m Hm,
    have H1 := Hx (1/m),
    rw ←inv_eq_one_div at Hm,
    have H2 : n ≤ m,
    { suffices : ↑n < (↑m:ℝ),exact le_of_lt (nat.cast_lt.1 this), exact lt_of_le_of_lt (le_max_right _ _) Hm },
    have H4 : 1 / (↑m:ℝ) ∈ {x : ℝ | ∃ (m : ℕ) (H : m ≥ n), x = a2 ⟨m, (le_trans Hn H)⟩},
    { existsi [m,H2],
      refl },
    have H5 := H1 H4,
    have H6 := inv_le_inv _ _ Hny H5,
    rw [←inv_eq_one_div,inv_inv'] at H6,
    apply lt_irrefl (m:ℝ),
    refine lt_of_le_of_lt H6 _,
    refine lt_of_le_of_lt (le_max_left _ _) Hm,
end


--noncomputable def a3 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1 - ((((N.val % (2:ℕ))):ℤ):ℝ)
theorem Q6c3' : liminf a3 0 :=
begin
existsi (λ _,(0:ℝ)),
split,
{ split,
  { intros x₁ Hx₁,
    cases Hx₁ with n₁ Hn₁,
    cases Hn₁ with H1 H2,
    rw H2,
    exact le_refl 0 },
  intros x₂ Hx₂,
  apply Hx₂,
  existsi 1,
  existsi _,refl,
  exact le_refl 1 },
intros n H,
split,
{ intro x₁,
  intro H1,
  show 0 ≤ x₁,
  cases H1 with n₁ Hn₁,
  cases Hn₁ with H1 H2,
  rw H2,
  unfold a3,
  rw [sub_nonneg],
  show ↑((↑n₁:ℤ) % (↑2:ℤ)) ≤ (1:ℝ),
  have H3 : (1:ℝ) = ↑(1:ℤ), rw [←int.cast_one],
  rw [H3],
  rw [int.cast_le],
  apply int.le_of_lt_add_one,
  show ↑n₁ % ↑2 < (2:ℤ),
  refine int.mod_lt_of_pos ↑n₁ _,
  norm_num },
intros x₁ Hx₁,
show x₁ ≤ 0,
apply Hx₁,
existsi (2*n+1),
existsi _,
{ unfold a3,
  apply eq.symm,
  apply sub_eq_zero_of_eq,
  rw ←int.cast_one,
  rw int.cast_inj,
  show (1:ℤ) = ↑((2*n+1) % 2),
  suffices : 1 = 1 % 2,simpa,
  refl },
rw [mul_comm,mul_two,add_assoc],
apply nat.le_add_right
end 