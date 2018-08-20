import data.nat.basic M3P14.order_zmodn_kmb data.int.basic

private theorem aux1 (a : ℕ): 
    1 < nat.succ (nat.succ a) := 
begin
    suffices : 1 < (nat.succ a) + 1, by simp [this],
    suffices : 0 < (nat.succ a), rwa lt_add_iff_pos_left,
    suffices : 0 ≠ (nat.succ a), from (nat.pos_iff_ne_zero.mpr this.symm),
    trivial,
end

private theorem aux2 (a b : ℕ) (h : a + 3 ≥ int.nat_abs ↑b) : 
    (a + 3) % (nat.succ b) < nat.succ (nat.succ (nat.succ a)) := 
begin
    simp at h,
    have neg : (nat.succ b) ≠ 0, trivial,
    have : (a + 3) % (nat.succ b) < (nat.succ b), from nat.mod_lt (a + 3) (nat.pos_iff_ne_zero.mpr neg),
    --suffices : b < nat.succ (nat.succ (nat.succ a)), from 
    sorry,
end


private theorem aux3 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
    2 < nat.succ (nat.succ (nat.succ a)) := 
begin
    suffices : 2 < (nat.succ a) + 2, by simp [this],
    suffices : 0 < (nat.succ a), rwa lt_add_iff_pos_left,
    suffices : 0 ≠ (nat.succ a), from (nat.pos_iff_ne_zero.mpr this.symm),
    trivial,
end

private theorem aux4 (a b : ℕ) : 
    (a + 3) / 2 < nat.succ (nat.succ (nat.succ a)) := 
begin
    suffices : (a + 3) / 2 < (a+3), by simp [this],
    sorry,
end

private theorem aux5 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
    b % (a + 3) < nat.succ (nat.succ (nat.succ a)) := 
begin
    simp at h,
    suffices : (a+3) > 0, from nat.mod_lt b this,
    suffices : 0 ≠ (a+3), from (nat.pos_iff_ne_zero.mpr this.symm),
    trivial,
end

private def jacobi_sym_pos : ℕ → ℕ → ℤ
| a          0 := 0
| 0          (nat.succ b) := 0
| 1          (nat.succ b) := 1
| 2          (nat.succ b) := if (nat.succ b) % 8 = 1 ∨ (nat.succ b) % 8 = 7 then 1 else -1
| (nat.succ (nat.succ (nat.succ a))) (nat.succ b) := 
                if h1 : (a+3) ≥ int.nat_abs (nat.succ b) then 
                have (a + 3) % (nat.succ b) < nat.succ (nat.succ (nat.succ a)), from aux2 a b h1, 
                jacobi_sym_pos ((a+3)%(nat.succ b)) (nat.succ b) else
                (if h2 : (a+3) % 2 = 0 then 
                have 2 < nat.succ (nat.succ (nat.succ a)), from aux3 a (nat.succ b) h1, 
                have (a + 3) / 2 < nat.succ (nat.succ (nat.succ a)), from aux4 a (nat.succ b), 
                jacobi_sym_pos 2 (nat.succ b) * jacobi_sym_pos ((a+3)/2) (nat.succ b) else 
                have (nat.succ b) % (a + 3) < nat.succ (nat.succ (nat.succ a)), begin sorry end,
                (if (a+3) % 4 = 1 ∨ (nat.succ b) % 4 = 1  then jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3) else -(jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3))))
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (psigma.fst)⟩ ]}

private def jacobi_sym_aux : ℤ → ℤ → ℤ
| a     -[1+b] := 0
| (-1)       b := if b % 4 = 1 then 1 else -1 
| -[1+(nat.succ a)] b := 
                have 1 < nat.succ (nat.succ a), from aux1 a, 
                jacobi_sym_pos (a+2) (int.nat_abs b) * jacobi_sym_aux (-1) b
| a          b := jacobi_sym_pos (int.nat_abs a) (int.nat_abs b)
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ psigma.fst)⟩ ]}

/- Computes the Jacobi Symbol, extended to b even which will output 0, is it the Kronecker Symbol?-/
def jacobi_sym : ℤ → ℤ → ℤ
| a          1 := 1
| a          b := if b % 2 = 1 then jacobi_sym_aux a b else 0


#eval jacobi_sym 8 1
#eval jacobi_sym (-5 : ℤ) 0
#eval jacobi_sym (-1 : ℤ) 0
#eval jacobi_sym (-2 : ℤ) 15
#eval jacobi_sym (-5 : ℤ) 8
#eval jacobi_sym 1236 200011



