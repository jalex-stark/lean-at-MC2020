import tactic
import data.nat.basic
import data.nat.prime
import data.real.basic
import data.real.irrational


noncomputable theory
open_locale classical

lemma two_dvd_of_two_dvd_sq (m n : ℕ) : 2 * m^2 = n^2 → 2 ∣ n :=
begin
  intros eq₁,
  have : 2 ∣ n^2, by { use m^2, exact eq.symm eq₁},
  exact nat.prime.dvd_of_dvd_pow nat.prime_two ‹2 ∣ n^2 ›,
end


lemma gcd_div_left (a b : ℕ) : (nat.gcd a b) ∣ a :=
begin
  refine nat.gcd_eq_right_iff_dvd.mpr _,
  rw h, simp only [nat.gcd_gcd_self_right_left],
end


-- maynbe the next one is a level and the previous one is provided?
lemma gcd_div_right (a b : ℕ) : (nat.gcd a b) ∣ b :=
begin
  rw nat.gcd_comm, apply gcd_div_left,
end


-- i think the following two lemma can be "levels". 
lemma eq_zero_of_sq_eq_zero (m : ℕ) (hm : m^2 = 0) : m = 0 :=
begin
  simp only [nat.pow_two] at hm, 
  simp only [nat.mul_eq_zero, or_self] at hm,
  assumption,
end

lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m^2 = 0 ↔ m = 0 :=
begin
  split, 
    { apply eq_zero_of_sq_eq_zero },
    intro h, rw h, ring,
end

-- this lemma needs a better name
lemma gcd_spec 
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

lemma wlog_nonzero (m n : ℕ) (hm : m ≠ 0) (hmn : 2 * m^2 = n^2) : n ≠ 0 :=
begin
  contrapose! hm,
  rw hm at hmn, ring at hmn,
  rw ← sq_eq_zero_iff_eq_zero,
  rw nat.mul_eq_zero at hmn,
  norm_num at hmn, exact hmn,
end

lemma wlog_gcd' (m n : ℕ) (hm : m ≠ 0) (hmn : 2 * m^2 = n^2) : 
∃ m' n', nat.coprime m' n' ∧ m' ≠ 0 ∧ 2 * m'^2 = n'^2 :=
begin
  -- i don't really know the difference between set and let, 
  -- but i think set usually works better for me
  set k := m.gcd n,
  have hkm : k ∣ m := gcd_div_left m n, 
  have hkn : k ∣ n := gcd_div_right m n, 
  have hn : n ≠ 0 := wlog_nonzero _ _ hm hmn,
  have hk : k ≠ 0, 
    { rw ← nat.pos_iff_ne_zero,
    apply nat.gcd_pos_of_pos_left,
    rwa nat.pos_iff_ne_zero },
  cases hkm with m' hkm,
  cases hkn with n' hkn,
  use m', use n',
  split, apply gcd_spec m n m' n' k,
    simp,
    assumption,
    assumption,
    rwa nat.pos_iff_ne_zero,
    rwa nat.pos_iff_ne_zero,
  split,
    rw hkm at hm, contrapose! hm, rw hm, ring,
  rw [hkn, hkm] at hmn, ring_exp at hmn, 
  rw nat.mul_right_inj at hmn,
  finish,
  rw nat.pos_iff_ne_zero, contrapose! hk,
  rwa ← sq_eq_zero_iff_eq_zero, 
  -- assumption doesn't work here... yikes!
  finish,
end

lemma wlog_gcd : --(p q : ℕ) (q_ne_zero : q ≠ 0) (h : nat.coprime p q) (hpq : 2 * q^2 = p^2): 
¬( ∃ p q : ℕ,
     q ≠ 0 ∧
     nat.gcd p q = 1∧ 
     2 * q^2 = p^2) →
¬( ∃ p q : ℕ,
     q ≠ 0 ∧
     2 * q^2 = p^2):= 
begin 
  contrapose!,
  intros,
  cases a with p h,
  cases h with q h, 
  cases h with q_ne_zero rational_2,

  let k:= nat.gcd p q,
  have : (∃ p' q' : ℕ, p = k * p' ∧ q = k * q' ∧ nat.coprime p' q'), by sorry, --
  cases this with p' this, 
  cases this with q' this, 
  cases this with hp this,
  cases this with hq hpq,
  have q'_ne_zero: q' ≠ 0, by sorry, --
  have : 2 * q'^2 = p'^2, by sorry, --
  use [p',q', q'_ne_zero, hpq, this],
end 

#check nat.le_of_dvd
theorem sqrt2_irrational_aux (p q : ℕ) (hp : p ≠ 0) : 
2 * p^2 ≠ q^2 :=
begin
  intro hpq,
  -- have hq : q ≠ 0, apply wlog_nonzero _ _ hp hpq,
  have key := wlog_gcd' p q hp hpq,
  rcases key with ⟨ m , n, hmn' , hm , hmn ⟩ ,
  clear' hpq hp p q,
  unfold nat.coprime at hmn',
  have h2m : 2 ∣ n,
  apply two_dvd_of_two_dvd_sq, exact hmn,
  suffices key : 2 ∣ m,
    { have := nat.dvd_gcd key h2m, 
    replace this := nat.le_of_dvd _ this; linarith },
    
  -- have h2m' := h2m,
  cases h2m with n' hn',
  rw hn' at hmn, ring_exp at hmn, norm_num at hmn,
  have : 2 * n'^2 = m^2 := by linarith,
  apply two_dvd_of_two_dvd_sq, exact this,
end

theorem sqrt2_irrational'' : 
¬( ∃ p q : ℕ,
      q ≠ 0 ∧
      2 * p^2 = q^2) :=
begin
  push_neg,
  intros, 
  by_cases hq : q = 0, 
    {left, exact hq}, right,
  exact sqrt2_irrational_aux _ _ hq,
end

theorem sqrt2_irrational' : 
¬( ∃ p q : ℕ,
      q ≠ 0 ∧
      2 * q^2 = p^2) :=
begin
apply wlog_gcd,
by_contradiction h,

  cases h with p h, 
  cases h with q h, 
  cases h with q_ne_zero h, 
  cases h with coprime_pq h,
    

  have eq₂: 2 ∣ p := two_dvd_of_two_dvd_sq q p h,

  have eq₂' := eq₂,

  cases eq₂ with p₁ eq₂,

  rw eq₂ at h,

  have : 0 < 2, by {simp only [nat.succ_pos']},
  have eq₃: q^2 = 2 * p₁^2,
    {apply (nat.mul_right_inj this).1, ring at *, assumption},

  have eq₄: 2 * p₁^2 = q^2,
    by { exact eq.symm eq₃},

  have eq₅: 2 ∣ q,
    exact two_dvd_of_two_dvd_sq p₁ q eq₄,

  have eq₆: 2 ∣ 1,
  { suffices : 2 ∣ p.gcd q,
    rw coprime_pq at this,
    assumption,
    exact nat.dvd_gcd eq₂' eq₅},

  rw nat.dvd_one at eq₆,
-- I don't think I want to tell campers to use injections on arithmetic goals
-- that feels like too much of an implementation detail of the natural numbers
  injections,
end



-- looks like it is will be a lot of work to move to reals from here, not sure if it is worth the effort
-- the above theorem looks good enough to me

-- lemma rat.not_irrational (q : ℚ) : ¬irrational q := λ h, h ⟨q, rfl⟩
-- def irrational (x : ℝ) := x ∉ set.range (coe : ℚ → ℝ)

lemma real_rat_irrat (r:real) : (∃ q: ℚ , r = q) ∨ irrational r := 
begin 
sorry,
end 

#check real_rat_irrat (real.sqrt 2) 

theorem sqrt2_irrational: (irrational (real.sqrt 2)) := 
begin 
sorry,
end