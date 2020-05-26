import data.real.basic
import data.real.irrational
import tactic

local attribute [instance] classical.prop_decidable

theorem sqrt_2_irrational : irrational (real.sqrt 2) :=
begin
  unfold irrational,
  by_contradiction,
  have sqrt_2_rational': ∃ m n : ℤ, int.gcd m n = 1 ∧ real.sqrt 2 = m / n, by sorry,
  have sqrt_2_rational: ∃ m n : ℕ, nat.gcd m n = 1 ∧ real.sqrt 2 = m / n, by sorry,
  cases sqrt_2_rational with m, 
  cases sqrt_2_rational_h with n,
  cases sqrt_2_rational_h_h with coprime sqrt_2_rational,
  have : 2 * (n:real)^2 = (m:real)^2, 
  begin 
    calc 
    2 * (n:real)^2 = (real.sqrt 2)^2 * n^2 : by sorry 
    ...     = (m / n)^2 * n^2 : by sorry 
    ...     = m^2 : by sorry,
  end,
  have : 2 * n^2 = m^2, by sorry, --cast_inj 
  have : 2 ∣ m, by sorry, 
  have : 2 ∣ n, by sorry,
  have not_coprime : 2 ∣ nat.gcd m n, 
  begin 
    exact nat.dvd_gcd ‹2 ∣ m› ‹2 ∣ n›,
  end, 
  rw coprime at not_coprime,
  exact nat.prime.not_dvd_one (nat.prime_two) not_coprime,
end 

