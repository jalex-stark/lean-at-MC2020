import data.nat.prime
import data.nat.parity
import tactic

-- include all of this as exercises on day 2

-- can you do this in tactic mode with only intro, apply, and exact?
theorem (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
begin
  rw classical.not_not,
end

lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
begin
  cases nat.prime.eq_two_or_odd hp, {assumption},
  rw ← nat.not_even_iff at h, contradiction,
end


#check @nat.even_add
-- tauto
lemma even_of_odd_add_odd
  {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
nat.even (a + b) :=
begin
  rw nat.even_add, tauto,
end

lemma one_lt_of_nontrivial_factor 
  {b c : ℕ} (hb : b < b * c) :
1 < c :=
begin
  contrapose! hb, 
  interval_cases c,
end

lemma nontrivial_product_of_not_prime
  {k : ℕ} (hk : ¬ k.prime) (two_le_k : 2 ≤ k) :
∃ a b < k, 1 < a ∧ 1 < b ∧ a * b = k :=
begin
  have h1 := nat.exists_dvd_of_not_prime2 two_le_k hk,
  rcases h1 with ⟨a, ⟨b, hb⟩, ha1, ha2⟩,
  use [a, b], norm_num, 
  split, assumption,
  split, rw [hb, lt_mul_iff_one_lt_left], linarith, 
  sorry,
  split, linarith,
  split, rw hb at ha2, apply one_lt_of_nontrivial_factor ha2,
  rw hb,
end


theorem three_fac_of_sum_consecutive_primes 
  {p q : ℕ} (hp : p.prime) (hq : q.prime) (hpq : p < q) 
  (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
  (consecutive : ∀ k, p < k → k < q → ¬ k.prime) :
∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 :=
begin
  use 2, have h1 : nat.even (p + q), 
  
  { apply even_of_odd_add_odd,
    contrapose! p_ne_2, apply eq_2_of_even_prime; assumption,
    contrapose! q_ne_2, apply eq_2_of_even_prime; assumption },
  cases h1 with k hk, 
  have hk' : ¬ k.prime, apply consecutive, linarith, linarith,
  have h2 := nat.exists_dvd_of_not_prime2 _ hk',
  swap, { linarith [nat.prime.two_le hp] },
  rcases h2 with ⟨b, hb, hb1, hb2⟩,
  cases hb with c hc,
  use [b, c], 
  split, { rw [hk, hc], ring }, -- ring should get introduced in day 2
  norm_num,
  split, linarith, rw hc at hb2,
  exact one_lt_of_nontrivial_factor hb2,
end