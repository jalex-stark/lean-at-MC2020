import tactic
import data.nat.prime
import data.int.modeq
import data.zmod.basic

noncomputable theory
open_locale big_operators
open finset
/-
In the first class we proved that there are infinitely many primes.
This problem asks for an alternative proof.
Let a_n = 2^2^n + 1. Prove that for any positive integer k we have
∏_{j=0}^{k−1} a_j = a_k − 2, and then explain why this implies that there are infinitely many primes.
-/
section problem1

-- calling the output of a an integer makes it much easier to do arithmetic.
def a (n : ℕ) : ℤ := 2 ^ 2 ^ n + 1

lemma a_prod (k : ℕ) : ∏ j in range k, a j = a k - 2 :=
begin
  -- Our induction principle (that is, a theorem that mathlib has proved by induction)
  -- says we just need to check the 0th term and ratios between terms.
  revert k, apply prod_range_induction,
  -- the base case just requries funolding the definition of a and doing very simple arithmetic
  -- refl can do both of those
  -- { refl },
  -- we could also break it into two steps with tools that run more quickly
  { unfold a, norm_num },
  intro n, unfold a,
  -- all that's left is straigthforward algebraic manipulation
  ring_exp,
end

lemma b {p : ℤ} (hp : 2 < p) (a b k : ℤ) (ha : a = k * b + 2) :
p ∣ b → ¬ p ∣ a :=
begin
  intro hb,
  cases hb with b' hb, rw hb at ha,
  have key : a ≡ 2 [ZMOD p],
  rw ha, ring,
  refine int.modeq.modeq_iff_dvd.mpr _,
  use -k * b', ring,
  sorry,
end

end problem1

section problem2


lemma sq_mod_8 (a : ℤ) : a^2 % 8 ∈ [(0:ℤ),1,4] := sorry

lemma part_a_hint (a b c : zmod 8) : a^2 + b^2 + c^2 ≠ 999 := sorry

-- this is the part we really want, the above are hints.
lemma part_a (a b c : ℤ) : a^2 + b^2 + c^2 ≠ 999 := sorry


lemma sum_congr_mod
{α : Type*} (n : ℕ) (m : ℤ) (s r : ℕ → ℤ) (h : ∀ a ∈ range n, s a ≡ r a [ZMOD m]) :
∑ k in range n, s k ≡ ∑ k in range n, r k [ZMOD m] :=
begin
  induction n with d hd, simp,
  rw sum_range_succ,
  rw sum_range_succ,
  sorry,
end

lemma part_b (n : ℕ) (x : ℤ → ℤ) :
∑ k in range n, (x k) * 10^k ≡ ∑ k in range n, (x k) * (-1)^k [ZMOD 11] :=
begin
  sorry,
end

end problem2
