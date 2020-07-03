import tactic
import data.nat.basic
import data.nat.prime
import data.real.basic
import data.real.irrational


noncomputable theory
open_locale classical

-- have them prove it assuming as much of the technical assumption


lemma two_dvd_of_two_dvd_sq {n : ℕ} (hn : 2 ∣ n ^ 2) : 2 ∣ n :=
begin
  apply nat.prime.dvd_of_dvd_pow, 
  { exact nat.prime_two },
  exact hn,
end

lemma two_dvd_of_two_dvd_sq' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ n :=
begin
  apply two_dvd_of_two_dvd_sq,
  use m^2, rw hmn,
end

example (a b c : ℕ) (hc : 0 < c) (h : c * a = c * b) : a = b :=
begin
  -- library_search succeeds here
  rwa nat.mul_right_inj at h, 
  assumption,
end

lemma two_dvd_of_two_dvd_sq'' {m n : ℕ} (hmn : 2 * m ^ 2 = n ^ 2) : 2 ∣ m :=
begin
  apply two_dvd_of_two_dvd_sq,
  have hn := two_dvd_of_two_dvd_sq' hmn,
  cases hn with k hk,
  use k^2, 
  rw hk at hmn, clear hk,
  have : 0 < 2 := by norm_num,
  rw ← nat.mul_right_inj this, 
  ring at hmn, ring, assumption,
end



lemma gcd_div_left (a b : ℕ) : (nat.gcd a b) ∣ a :=
begin
  rw nat.gcd_eq_right_iff_dvd,
  apply nat.gcd_gcd_self_right_left,
end


-- maynbe the next one is a level and the previous one is provided?
lemma gcd_div_right (a b : ℕ) : (nat.gcd a b) ∣ b :=
begin
  rw nat.gcd_comm, apply gcd_div_left,
end


-- i think the following two lemma can be "levels". 
lemma eq_zero_of_sq_eq_zero (m : ℕ) (hm : m ^ 2 = 0) : m = 0 :=
begin
  simp only [nat.pow_two] at hm, 
  simp only [nat.mul_eq_zero, or_self] at hm,
  assumption,
end

lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m ^ 2 = 0 ↔ m = 0 :=
begin
  split, 
    { apply eq_zero_of_sq_eq_zero },
    intro h, rw h, ring,
end

-- this lemma needs a better name
lemma coprime_of_div_gcd 
  (m n m' n' k : ℕ) 
  (hk : k = nat.gcd m n)
  (hmk : m = k * m')
  (hnk : n = k * n')
  (hm : 0 < m)
  (hn : 0 < n)
: nat.coprime m' n' :=
begin
  unfold nat.coprime,
  have key := nat.gcd_mul_left k m' n',
  rw [← hmk, ← hnk, ← hk] at key,
  symmetry' at key,
  rwa nat.mul_right_eq_self_iff at key,
  rw hk,
  apply nat.gcd_pos_of_pos_left,
  exact hm,
end

-- i think lemmas in the library usually use 0 < n instead of n ≠ 0.

lemma wlog_nonzero {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m^2 = n^2) : n ≠ 0 :=
begin
  contrapose! hm,
  rw hm at hmn, ring at hmn,
  rw ← sq_eq_zero_iff_eq_zero,
  rw nat.mul_eq_zero at hmn,
  norm_num at hmn, exact hmn,
end

lemma wlog_gcd (m n : ℕ) (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : 
∃ m' n', nat.coprime m' n' ∧ m' ≠ 0 ∧ 2 * m' ^ 2 = n' ^ 2 :=
begin
  -- i don't really know the difference between set and let, 
  -- but i think set usually works better for me
  set k := m.gcd n,
  -- simp only [nat.pow_eq_pow] at hmn,
  have hkm : k ∣ m := gcd_div_left m n, 
  have hkn : k ∣ n := gcd_div_right m n, 
  have hn : n ≠ 0 := wlog_nonzero hm hmn,
  have hk : k ≠ 0, 
    { rw ← nat.pos_iff_ne_zero,
    apply nat.gcd_pos_of_pos_left,
    rwa nat.pos_iff_ne_zero },
  cases hkm with m' hkm,
  cases hkn with n' hkn,
  use [m', n'],
  split, apply coprime_of_div_gcd m n m' n' k,
  -- this generates a bunch of conditions we'll tackle one at a time
    { simp },
    { assumption },
    { assumption },
    { rwa nat.pos_iff_ne_zero },
    { rwa nat.pos_iff_ne_zero },
  split,
  { rw hkm at hm, contrapose! hm, rw hm, ring },
  contrapose! hmn,
  rw [hkn, hkm], ring, 
  rw nat.mul_left_inj, { simpa }, 
  -- { rwa mul_comm, simp at hmn, simpa, },

  rw nat.pos_iff_ne_zero, 
  contrapose! hk,
  apply eq_zero_of_sq_eq_zero, 
  revert hk, simp,
end

lemma not_coprime_of_common_factor {m n k : ℕ} 
  (hk : 1 < k) (hm : m ≠ 0) (hn : n ≠ 0)  (hmk : k ∣ m) (hnk : k ∣ n) :
¬ nat.coprime n m :=
begin
  -- library_search,
  exact nat.not_coprime_of_dvd_of_dvd hk hnk hmk,
end

lemma sqrt2_irrational_aux {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m^2 = n^2) : false :=
begin
  have h2 := wlog_gcd _ _ hm hmn, clear hmn hm m n,
  rcases h2 with ⟨m, n, h , hm, hmn ⟩,
  contrapose h, clear h,
  have hn := wlog_nonzero hm hmn,
  have hn2 := two_dvd_of_two_dvd_sq' hmn,
  have : 1 < 2 := by norm_num,
  apply not_coprime_of_common_factor this,
  { assumption },
  { assumption },
  { assumption },
  apply two_dvd_of_two_dvd_sq'',
  exact hmn,
end

theorem sqrt2_irrational : 
¬( ∃ p q : ℕ,
      p ≠ 0 ∧
      2 * p^2 = q^2) :=
begin
  push_neg,
  intros, 
  by_cases hp : p = 0, 
  { left, exact hp }, right,
  by_contra h, push_neg at h,
  apply sqrt2_irrational_aux hp h,
end
