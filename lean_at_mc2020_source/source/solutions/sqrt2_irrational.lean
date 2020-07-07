import tactic
import data.nat.basic
import data.nat.prime

noncomputable theory
open_locale classical

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
  rw nat.gcd_comm, 
  apply gcd_div_left,
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

lemma coprime_of_div_gcd 
  (m n m' n' k : ℕ) 
  (hk : k = nat.gcd m n)
  (hmk : m = k * m')
  (hnk : n = k * n')
  (hm : 0 < m)
  (hn : 0 < n)
: nat.coprime m' n' :=
begin
  have key := nat.gcd_mul_left k m' n',
  rw [← hmk, ← hnk, ← hk] at key,
  symmetry' at key,
  rw nat.mul_right_eq_self_iff at key, exact key,
  -- generates side goal 0 < k
  rw hk,
  apply nat.gcd_pos_of_pos_left,
  exact hm,
end


lemma wlog_nonzero {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m^2 = n^2) : n ≠ 0 :=
begin
  contrapose! hm,
  rw hm at hmn, ring at hmn,
  rw ← sq_eq_zero_iff_eq_zero,
  rw nat.mul_eq_zero at hmn,
  norm_num at hmn, exact hmn,
end

lemma gcd_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : nat.gcd m n ≠ 0 :=
begin
  rw ← nat.pos_iff_ne_zero,
  apply nat.gcd_pos_of_pos_left,
  rwa nat.pos_iff_ne_zero, -- omega works
end

lemma ne_zero_of_mul_ne_zero {m k m' : ℕ}
  (hm : m ≠ 0)
  (hkm : m = k * m') :
  m' ≠ 0 :=
begin
  contrapose! hm, 
  rw hkm,
  rw hm, ring
end

lemma wlog_coprime_aux {m n k : ℕ}
  (hmn : 2 * (k * m) ^ 2 = (k * n) ^ 2)
  (hk : k ≠ 0) :
  2 * m ^ 2 = n ^ 2 :=
begin
  ring at *,
  rwa nat.mul_left_inj at hmn,  
  rw nat.pos_iff_ne_zero,
  contrapose! hk,
  apply eq_zero_of_sq_eq_zero, 
  ring at *,
  assumption,
end

lemma wlog_coprime {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ^ 2 = n ^ 2) : 
∃ m' n', m' ≠ 0  ∧  2 * m' ^ 2 = n' ^ 2 ∧ nat.coprime m' n' :=
begin
  set k := m.gcd n,
  -- We want to divide by k. To set that up, 
  -- we prove that k is not zero
  have hn : n ≠ 0 := wlog_nonzero hm hmn,
  have hk : k ≠ 0 := gcd_ne_zero hm hn,
  -- and we prove that k divides m and n
  have hkm : k ∣ m := gcd_div_left m n, 
  have hkn : k ∣ n := gcd_div_right m n, 
  -- here we extract the quotients m' and n'
  cases hkm with m' hkm,
  cases hkn with n' hkn,
  use [m', n'],
  split, -- ⊢	m' ≠ 0
  { apply ne_zero_of_mul_ne_zero hm hkm },
  split, -- ⊢	2 * m' ^ 2 = n' ^ 2
  { rw [hkm, hkn] at hmn,
    apply wlog_coprime_aux hmn,
    assumption },
  -- 	⊢	m'.coprime n'
  apply coprime_of_div_gcd m n m' n' k,
  -- this generates a bunch of conditions we'll tackle one at a time
  { refl }, -- this is true by definition of k
  { exact hkm },
  { exact hkn },
  { rw nat.pos_iff_ne_zero, exact hm },
  { rw nat.pos_iff_ne_zero, exact hn },
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
  have h2 := wlog_coprime hm hmn, clear hmn hm m n,
  rcases h2 with ⟨m, n, h , hm, hmn ⟩,
  contrapose h, clear h,
  have : 1 < 2, norm_num, -- linarith also works
  contrapose! hmn,
  apply not_coprime_of_common_factor this,
  { apply wlog_nonzero hmn, assumption, },
  { assumption },
  { apply two_dvd_of_two_dvd_sq', exact hm, },
  apply two_dvd_of_two_dvd_sq'',
  exact hm,
end

theorem sqrt2_irrational : 
¬ ∃ p q : ℕ,
  p ≠ 0 ∧ 2 * p^2 = q^2 :=
begin
  push_neg,
  intros, 
  by_cases hp : p = 0, 
  { left, exact hp }, right,
  by_contra h, push_neg at h,
  apply sqrt2_irrational_aux hp h,
end
