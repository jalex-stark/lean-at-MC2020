import data.nat.prime
import data.nat.parity
import tactic


example (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
begin
  intros nnnp p, apply nnnp, 
  intro np, apply np, 
  apply p,
end


example (p : ℕ) : p.prime → p = 2 ∨ p % 2 = 1 :=
begin
  library_search,
end

#check @nat.prime.eq_two_or_odd

lemma eq_two_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
begin
  cases nat.prime.eq_two_or_odd hp, {assumption},
  rw ← nat.not_even_iff at h, contradiction,
end


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
  
  rw ← mul_one b at hb,
  contrapose! hb, 
  suggest,
  interval_cases c,
  -- ⊢ b * 0 ≤ b
  simp, 
  -- ⊢ b * 1 ≤ b
  simp,
end
example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
begin
  split,
  {intros, linarith,},
  contrapose!,
  simp,
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
  cases b, {linarith}, {simp},
  split, linarith,
  split, rw hb at ha2, apply one_lt_of_nontrivial_factor ha2,
  rw hb,
end

-- norm_num, linarith
theorem three_fac_of_sum_consecutive_primes 
  {p q : ℕ} (hp : p.prime) (hq : q.prime) (hpq : p < q) 
  (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
  (consecutive : ∀ k, p < k → k < q → ¬ k.prime) :
∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 :=
begin
  use 2, have h1 : nat.even (p + q), 
  { apply even_of_odd_add_odd, 
    contrapose! p_ne_2, apply eq_two_of_even_prime; assumption, 
    contrapose! q_ne_2, apply eq_two_of_even_prime; assumption, },

  cases h1 with k hk, 
  have hk' : ¬ k.prime, 
  { apply consecutive; linarith },

  have h2k : 2 ≤ k, { have := nat.prime.two_le hp, linarith, },
  have h2 := nat.exists_dvd_of_not_prime2 _ hk',
  swap, { exact h2k }, -- for some reason I think it's interesting to have the student remember that they've already proved this
  rcases nontrivial_product_of_not_prime hk' h2k with ⟨ b, c, hbk, hck, hb1, hc1, hbc⟩,
  use [b,c],
  split, { rw [hk, ← hbc], ring },
  split, { norm_num },
  split; assumption,
end