import data.nat.basic M3P14.order_zmodn_kmb data.int.basic

theorem aux1 (a : ℕ) (b : ℤ) : 
    1 < nat.succ (nat.succ a):= 
begin
    suffices : 1 < (nat.succ a) + 1, by simp [this],
    suffices : 0 < (nat.succ a), rwa lt_add_iff_pos_left,
    suffices : 0 ≠ (nat.succ a), from (nat.pos_iff_ne_zero.mpr this.symm),
    trivial,
end

#check nat.pos_iff_ne_zero

def jacobi_sym_pos : ℕ → ℕ → ℤ
| 0          b := 0
| a     -[1+b] := 0
| 1          b := 1
| (-1)       b := if b % 4 = 1 then 1 else -1 
| 2          b := if b % 8 = 1 ∨ b % 8 = 7 then 1 else -1
| (nat.succ (nat.succ a)) b := 
                --have int.nat_abs 2 < int.nat_abs (1 + (1 + ↑a)), by sorry,
                --have int.nat_abs (↑a / 2 % b) < int.nat_abs (1 + (1 + ↑a)), by sorry,
                --have int.nat_abs (b % ↑a) < int.nat_abs (1 + (1 + ↑a)), by sorry,
                if h : (nat.succ (nat.succ a)) % 2 = 0 then jacobi_sym_pos 2 b * jacobi_sym_pos (((nat.succ (nat.succ a))/2) % b) b else 
                (if (nat.succ (nat.succ a)) % 4 = 1 ∨ b % 4 = 1 then jacobi_sym_pos (b % (nat.succ (nat.succ a))) (nat.succ (nat.succ a)) else -(jacobi_sym_pos (b % (nat.succ (nat.succ a))) (nat.succ (nat.succ a))))


def jacobi_sym : ℤ → ℤ → ℤ
| 0          b := 0
| a     -[1+b] := 0
| 1          b := 1
| (-1)       b := if b % 4 = 1 then 1 else -1 
| 2          b := if b % 8 = 1 ∨ b % 8 = 7 then 1 else -1
| -[1+(nat.succ (nat.succ a))]     b := jacobi_sym_pos (nat.succ (nat.succ a)) b * jacobi_sym (-1) b
| (nat.succ (nat.succ a))          b := jacobi_sym_pos (nat.succ (nat.succ a)) b


using_well_founded{rel_tac:= λ _ _, `[exact ⟨_, measure_wf (int.nat_abs∘ psigma.fst)⟩ ]}



#exit

-- make it handle neg number once, then do all the positive stuff
def jacobi_sym : ℤ → ℤ → ℤ
| a     -[1+b] := 0
| 0          b := 0
| 1          b := 1
| (-1)       b := if b % 4 = 1 then 1 else -1 
| 2          b := if b % 8 = 1 ∨ b % 8 = 7 then 1 else -1
| -[1+ (nat.succ a)]     b := 
                have int.nat_abs (int.succ ↑a % b) < nat.succ (nat.succ a), begin sorry end,
                have 1 < nat.succ (nat.succ a), from aux1 a b,
                jacobi_sym (int.succ a % b) b * jacobi_sym (-1) b
| (nat.succ (nat.succ a)) b := 
                have int.nat_abs 2 < int.nat_abs (1 + (1 + ↑a)), by sorry,
                have int.nat_abs (↑a / 2 % b) < int.nat_abs (1 + (1 + ↑a)), by sorry,
                have int.nat_abs (b % ↑a) < int.nat_abs (1 + (1 + ↑a)), by sorry,
                if h : a % 2 = 0 then jacobi_sym 2 b * jacobi_sym ((a/2) % b) b else 
                (if a % 4 = 1 ∨ b % 4 = 1 then jacobi_sym (b % a) a else -(jacobi_sym (b % a) a))

using_well_founded{rel_tac:= λ _ _, `[exact ⟨_, measure_wf (int.nat_abs∘ psigma.fst)⟩ ]}

#eval jacobi_sym 1 (-5 : ℤ)

#eval jacobi_sym (-5 : ℤ) (-4 : ℤ)

#eval jacobi_sym (-1 : ℤ) 9
#eval jacobi_sym (-2 : ℤ) 15

#eval jacobi_sym (-5 : ℤ) 8
