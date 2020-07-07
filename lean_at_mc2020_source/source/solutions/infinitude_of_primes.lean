import tactic
import data.nat.prime

open nat

theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ prime p :=          
begin
  set p := min_fac (n.fact + 1), use p,
  have pp : p.prime, 
  { exact min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos n))) },
 
  split,
  swap, exact pp,

  have hp := pp.not_dvd_one,
  contrapose! hp,
  -- by_contradiction hp,
  have hp₁: p ∣ n.fact, 
  { apply dvd_fact, { apply min_fac_pos }, linarith, },
  rw nat.dvd_add_iff_right, -- this solution creates a metavariable, so is not what I expect students to find.
  apply min_fac_dvd, assumption,
  -- exact (nat.dvd_add_iff_right hp₁).2 (fact n + 1).min_fac_dvd,
end