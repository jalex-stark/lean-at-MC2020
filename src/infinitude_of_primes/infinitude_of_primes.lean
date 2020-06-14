import tactic
import data.nat.prime

open nat

theorem exists_infinite_primes (n : ℕ) : ∃ p, p ≥ n ∧ prime p :=          
begin
  let p:= min_fac (n.fact + 1), use p,
  have pp : p.prime, from min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos n))),
 
  split,
  show p.prime, from pp,
  
  by_contradiction hp,
  have hp₁: p ∣ n.fact, from dvd_fact (min_fac_pos (n.fact + 1)) (le_of_not_ge hp),
  have hp₂: p ∣ 1, from (nat.dvd_add_iff_right hp₁).2 (fact n + 1).min_fac_dvd,
  exact pp.not_dvd_one hp₂,
end