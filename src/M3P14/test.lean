import data.nat.basic tactic.norm_num
variables p q : ℕ

theorem haha (h : p-1 = p*(p-1)) : p-1 = 0 :=
begin
    calc
    p-1 = p*(p-1) : h
    ... = p^2*1 - p^2*(1/p) : by rw nat.mul_sub_left_distrib
    ... = p^2 - p^2*(1/p) : by rw nat.mul_one
    ... = p^2 - p^(1+1)*(1/p) : by simp
    ... = p^2 - p^1*p^1*(1/p) : by rw nat.pow_add
    ... = p^2 - p*p*(1/p) : by simp
    ... = p^2 - p*1*(p/p) : by rw mul_div_comm  
    ... = 0 : sorry
end

#check mul_div_cancel
#check 
