import tactic
import data.int.basic


-- a rw puzzle?
example 
  (p : ℕ → Prop) (n : ℕ) (hn : p n) 
  (h8 : ∀ n, p n ↔ p (n + 8))
  (h3 : ∀ n, p (n + 3) ↔ p n) :
p (n + 1) :=
begin
  rw ← h3 at hn,
  rw ← h3 at hn,
  rw ← h3 at hn,
  rw h8,
  exact hn,
end

-- 
example : fin 0 ≠ fin 1 :=
begin
  have : ∃ b : fin 1, true, 
  use 0,
  intro h,
  rw ← h at this,
  cases this with k hk,
  cases k, linarith,
end

-- when i started i thought this would be a rw puzzle, but it's not
theorem reflexive_of_symmetric_and_transitive (r : ℕ → ℕ → Prop)
  (h_symm : symmetric r) (h_trans : transitive r) 
  (h_connected : ∀ x, ∃ y, r x y) : 
reflexive r :=
begin
  intro x,
  have hxy := h_connected x,
  cases hxy with y hy,
  apply h_trans hy,
  apply h_symm hy,
end


lemma even_or_odd (n : ℕ) : 
(∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 :=
begin
  induction n with d hd, 
  { use 0, simp },
  -- you should ~always do this rw after opening the successor case of induction on the naturals
  rw nat.succ_eq_add_one,
  cases hd with h_even h_odd,
  { cases h_even with k hk, 
    right, use k, rw hk },
  cases h_odd with k hk,
  left, use k+1, rw hk, ring,
end

-- I don't think I can do this without coercions
example 
  (p : ℤ → Prop)
  (p_succ : ∀ n, p n → p (n + 1)) 
  (p_pred : ∀ n, p n → p (n - 1)) :
(∀ n, p n) ↔ p 0 :=
begin
  have key1 : ∀ n, p n ↔ p (n+1),
  { intro, split; intro h,
    { apply p_succ, assumption },
    have := p_pred (n+1), 
    ring at this, apply this, assumption },
  split; intro h, { apply h },
  intro n, cases n, -- rintro ⟨n⟩ also works
  { induction n with d hd, {simpa},
    rw nat.succ_eq_add_one,
    simp only [int.coe_nat_succ, int.of_nat_eq_coe],
    rwa ← key1 },
  induction n with d hd, { rw key1, simpa },
  rw nat.succ_eq_add_one, 
  rw key1, simpa,
end

-- by landing in ℤ, we avoid the perils of nat subtraction
def f : ℕ → ℕ
| 0 := 0
| (n + 1) := n + 1 + f n

example : f 1 = 1 := 
begin
  unfold f,
end

example (n : ℕ) : 2 * f n = n * (n + 1) :=
begin
  induction n with d hd,  
  -- base case
  { unfold f, simp },
  rw nat.succ_eq_add_one,
  unfold f, ring, 
  rw hd, ring,
end

open_locale big_operators
open finset
variables {R : Type*} [comm_ring R]

example (n : ℕ) (a : R) : 
(1 - a) * ∑ k in range n, a ^ k = 1 - a ^ n :=
begin
  rw mul_sum, apply sum_range_induction,
  { simp },
  intro, ring,
end

-- doing your induction "by hand"
example (n : ℕ) (a : R) : 
(1 - a) * ∑ k in range n, a^k = 1 - a ^n :=
begin
  induction n with d hd,
  { simp },
  rw [sum_range_succ, mul_add, hd, nat.succ_eq_add_one],
  ring_exp,
end
