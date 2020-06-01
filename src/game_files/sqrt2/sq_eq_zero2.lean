lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m^2 = 0 ↔ m = 0 :=
begin
  split, 
    { apply eq_zero_of_sq_eq_zero },
    intro h, rw h, ring,
end