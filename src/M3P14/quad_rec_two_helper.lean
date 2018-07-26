import tactic.ring 

lemma quad_res_two (n : ℕ) : n % 8 = 1 ∨ n % 8 = 7 → ((n ^ 2 - 1) / 8 % 2 = 0) :=
begin
  intro H,
  have H2 := nat.mod_add_div n 8,
  cases H,
  { rw H at H2,
    rw ←H2,
    rw ←nat.dvd_iff_mod_eq_zero,
    suffices : ∀ t, 2 ∣ ((1 + 8 * t) ^ 2 - 1) / 8,
      exact this (n/8),
    intro t,
    existsi t+4*t*t,
    show (1 * (1 + 8 * t) * (1 + 8 * t) - 1) / 8 = 2 * (t + 4 * t * t),
    rw (show 1 * (1 + 8 * t) * (1 + 8 * t) = 8 * (2 * t + 8 * t * t) + 1, by ring),
    rw nat.add_sub_cancel,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  },
  { rw H at H2,
    rw ←H2,
    rw ←nat.dvd_iff_mod_eq_zero,
    suffices : ∀ t, 2 ∣ ((7 + 8 * t) ^ 2 - 1) / 8,
      exact this (n/8),
    intro t,
    existsi 3+7*t+4*t*t,
    show (1 * (7 + 8 * t) * (7 + 8 * t) - 1) / 8 = 2 * (3 + 7 * t + 4 * t * t),
    rw (show 1 * (7 + 8 * t) * (7 + 8 * t) = 8 * (6 + 14 * t + 8 * t * t) + 1, by ring),
    rw nat.add_sub_cancel,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  }
end 

lemma quad_nonres_two (n : ℕ) : n % 8 = 3 ∨ n % 8 = 5 → ((n ^ 2 - 1) / 8 % 2 = 1) :=
begin
  intro H,
  have H2 := nat.mod_add_div n 8,
  cases H,
  { rw H at H2,
    rw ←H2,
    suffices : ∀ t : ℕ, ((3 + 8 * t) ^ 2 - 1) / 8 % 2 = 1,
      exact this (n/8),
    intro t,
    have H3 : (1 + 2 * (4*t^2 + 3*t)) % 2 = 1,
      rw nat.add_mul_mod_self_left,exact dec_trivial,
    suffices : ((3 + 8 * t) ^ 2 - 1) / 8 = (1 + 2 * (4 * t ^ 2 + 3 * t)),
      rwa this,
    suffices : ((3 + 8 * t) ^ 2 - 1) = 8 * (1 + 2 * (4 * t ^ 2 + 3 * t)),
      rw this,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  },
  { rw H at H2,
    rw ←H2,
    suffices : ∀ t : ℕ, ((5 + 8 * t) ^ 2 - 1) / 8 % 2 = 1,
      exact this (n/8),
    intro t,
    have H3 : (1 + 2 * (4*t^2 + 5*t + 1)) % 2 = 1,
      rw nat.add_mul_mod_self_left,exact dec_trivial,
    suffices : ((5 + 8 * t) ^ 2 - 1) / 8 = (1 + 2 * (4 * t ^ 2 + 5 * t + 1)),
      rwa this,
    suffices : ((5 + 8 * t) ^ 2 - 1) = 8 * (1 + 2 * (4 * t ^ 2 + 5 * t + 1)),
      rw this,
    rw nat.mul_div_cancel_left _ (show 8 > 0, from dec_trivial),
    ring
  }
end 
