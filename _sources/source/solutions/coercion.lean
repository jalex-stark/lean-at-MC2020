import tactic data.rat
open_locale big_operators
open finset

theorem sqrt2' : ¬ (∃ m n : ℕ, m ≠ 0 ∧ 2 * m^2 = n ^2) := 
begin 
  sorry,
end   

theorem sqrt2 : ¬ (∃ m n : ℤ, m ≠ 0 ∧ 2 * m^2 = n ^2) := 
begin 
  by_contradiction,
  apply sqrt2',
  rcases a with ⟨m,n,hm, hmn⟩,
  use [m.nat_abs, n.nat_abs],
  split,
  exact int.nat_abs_ne_zero_of_ne_zero hm,
  have m1 := int.nat_abs_pow_two m,
  have n1 := int.nat_abs_pow_two n,
  rw ←m1 at hmn,
  rw ←n1 at hmn,
  norm_cast at hmn,
  exact hmn,
end   

lemma temp (n : ℤ) : n * n = n^2 := 
begin 
  ring,
end 

example : ¬ (∃ q : ℚ, 2 = q * q) :=
begin
  by_contradiction,
  cases a with q key,
  have := rat.eq_iff_mul_eq_mul.mp key,
  have triv : (2:ℚ).denom = 1, refl,
  rw triv at this,
  have triv : (2:ℚ).num = 2, refl,
  rw triv at this,
  rw rat.mul_self_denom at this,
  rw rat.mul_self_num at this,
  simp only [mul_one, int.coe_nat_zero, int.coe_nat_succ, zero_add, int.coe_nat_mul] at this,
  rw temp at this, rw temp at this,
  apply sqrt2,
  use q.denom, use q.num,
  split,
  norm_cast,
  exact rat.denom_ne_zero q,
  exact this,
  -- have : 2 * (↑(q.denom) ^2) = q.num ^2, rw ←temp,
end


example (p q : rat) : q.denom ≠ 0 := 
begin 
  exact rat.denom_ne_zero q
end 

example (m : int ) : m ^ 2 = (m.nat_abs)^2 := 
begin 
  exact (int.nat_abs_pow_two m).symm,
end 
