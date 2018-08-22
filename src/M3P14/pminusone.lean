import data.int.basic

example (p : ℤ) (q : 2 ∣ int.nat_abs (p - 1)) :
int.nat_abs ((p - 1) / 2) = int.nat_abs (p - 1) / 2 :=
begin
  cases q with d hd,
  have H : ∃ e, (p - 1) = 2 * e,
  cases (int.nat_abs_eq (p - 1)),
    existsi (d : ℤ),
    rw [h,hd],
    refl,
  existsi (- (d : ℤ)),
    rw [h,hd],
  rw int.coe_nat_mul,
  rw mul_neg_eq_neg_mul_symm,refl,

  cases H with e He,
  rw He,
  rw int.nat_abs_mul,
  rw int.mul_div_cancel_left,
  show _ = 2 * _ / _,
  rw nat.mul_div_cancel_left,
  exact dec_trivial,
  exact dec_trivial,
end