import data.nat.prime
import data.nat.modeq
import data.nat.parity
import tactic

-- set_option pp.notation false 
-- include all of this as exercises on day 2

-- can you do this in tactic mode with only intro, apply, and exact?
example (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
begin
  rw classical.not_not, tauto,
end



example (p : ℕ) : p.prime → p = 2 ∨ p % 2 = 1 :=
begin
  exact nat.prime.eq_two_or_odd,
end

#check @nat.prime.eq_two_or_odd

lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
begin
  cases nat.prime.eq_two_or_odd hp, {assumption},
  rw ← nat.not_even_iff at h, contradiction,
end


#check @nat.even_iff
#check @nat.mod_two_eq_zero_or_one
#check @nat.not_even_iff

#check @nat.even_add
#check @nat.modeq.modeq_add_cancel_right
#check @nat.modeq.modeq_add_cancel_left
-- ∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b + d [MOD n] → c ≡ d [MOD n]

-- lemma even_add : ∀ (m n : ℕ), (m + n).even ↔ (m.even ↔ n.even) :=
-- begin 
--   intros,
--   rw nat.even_iff,
--   rw nat.even_iff,
--   rw nat.even_iff,

--   split,
--   begin 
--     intros, 
--     split,
--     begin 
--       intros,
--       have : 0 = 0 + 0, by simp,
--       rw this at a,
--       exact @nat.modeq.modeq_add_cancel_left 2 m 0 n 0 a_1 a,
--     end,
--     begin 
--       intros, 
--       have : 0 = 0 + 0, by simp,
--       rw this at a,
--       exact @nat.modeq.modeq_add_cancel_right 2 m 0 n 0 a_1 a,
--     end,
--   end,
--   begin 
--     intros,
--     by_cases hp : m % 2 = 0, 
--     {rw hp at a,
--     have := (a.1 rfl),
--     exact @nat.modeq.modeq_add 2 m 0 n 0 hp this,},
--     {
--       repeat{rw ←nat.even_iff at *},
--       sorry,
--     },
--   end,
-- end 

-- tauto

example (p a b : ℕ) : (a % p) = (b % p) → (a = b % p) :=
begin 
  sorry,
end 

#check nat.add_mod_eq_add_mod_left

lemma even_of_odd_add_odd
  {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
nat.even (a + b) :=
begin
  -- rw nat.even_add, tauto,
  rw nat.not_even_iff at *,
  rw nat.even_iff at *,

    -- rw this,
    -- exact @nat.modeq.modeq_add 2 a 1 b 1 ha hb,
    sorry,
  simp,
end

lemma one_lt_of_nontrivial_factor 
  {b c : ℕ} (hb : b < b * c) :
1 < c :=
begin
  contrapose! hb, 
  interval_cases c,
end

example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
begin
  split,
  {intros, linarith,},
  contrapose!,
  simp,
  -- exact bot_lt_iff_ne_bot,
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
  { sorry },

  cases h1 with k hk, 
  have hk' : ¬ k.prime, 
  { sorry },

  have h2k : 2 ≤ k, { sorry },
  have h2 := nat.exists_dvd_of_not_prime2 _ hk',
  swap, { sorry },
  rcases nontrivial_product_of_not_prime hk' h2k with ⟨ b, c, hbk, hck, hb1, hc1, hbc⟩,
  use [b,c],
  sorry,
end