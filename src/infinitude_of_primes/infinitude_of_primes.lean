import tactic
import data.nat.prime
set_option trace.simp_lemmas true

open nat

#check @nat.dvd_sub
/-
infinitude_of_primes.lean:6:0: information check result
dvd_sub : ∀ {k m n : ℕ}, n ≤ m → k ∣ m → k ∣ n → k ∣ m - n
-/
#check @nat.le.intro
#check nat.le.dest

theorem dvd_sub2 (p a b : ℕ) : (p ∣ a) → (p ∣ a + b) → (p ∣ b) :=
begin 
  have H : a ≤ a + b, {simp,},
  have K : b = (a + b) - a, {simp,},
  intros,
  rw K,
  apply nat.dvd_sub,
  repeat {assumption,},
end 

#check fact_pos
/-
infinitude_of_primes.lean:24:0: information check result
fact_pos : ∀ (n : ℕ), 0 < n.fact
-/

#print nat.prime 
/-
infinitude_of_primes.lean:31:0: information print result
def nat.prime : ℕ → Prop :=
λ (p : ℕ), 2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p
-/

#print prime.not_dvd_one
/-
infinitude_of_primes.lean:38:0: information print result
theorem nat.prime.not_dvd_one : ∀ {p : ℕ}, p.prime → ¬p ∣ 1 :=
λ {p : ℕ} (pp : p.prime) (a : p ∣ 1), id_rhs false (not_le_of_gt pp.one_lt (le_of_dvd (of_as_true trivial) a))
-/

example (p:nat) (pp: p.prime) : 2 ≤ p :=
begin 
  cases pp,
  exact pp_left, 
end   

example (p:nat) (pp: 2 ≤ p) : ¬ p ∣ 1 :=
begin 
  contrapose! pp,
  have : p = 1,
  rw ←nat.dvd_one,
  exact pp, linarith,
end   


theorem exists_infinite_primes (n : ℕ) : ∃ p, prime p ∧ p ≥ n :=          
begin
  set p:= min_fac (n.fact + 1), use p,
  have key1 : p ∣ n.fact + 1, by exact min_fac_dvd (n.fact + 1),
  have pp: p.prime, 
  { 
    apply min_fac_prime,
    have := fact_pos n,
    linarith,
  },
  split, assumption,
  {
    by_contradiction,
    push_neg at a,
    have key2 : p ∣ n.fact, apply dvd_fact,
    exact min_fac_pos (n.fact + 1),
    linarith,
    have := dvd_sub2 p n.fact 1 key2 key1,
    exact prime.not_dvd_one pp this, -- can get rid of this
  },

  -- have pp : p.prime, from min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos n))),
 
  -- split,
  -- show p.prime, from pp,
  
  -- by_contradiction hp,
  -- have hp₁: p ∣ n.fact, from dvd_fact (min_fac_pos (n.fact + 1)) (le_of_not_ge hp),
  -- have hp₂: p ∣ 1, from (nat.dvd_add_iff_right hp₁).2 (fact n + 1).min_fac_dvd,
  -- exact pp.not_dvd_one hp₂,
end


/-
definitions:
	nat.prime 
	min_fac
	n.fact 

min_fac_prime 
fact_pos
dvd_fact
min_fac_pos
min_fac_dvd
not_dvd_one


-/
