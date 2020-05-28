import tactic
import data.nat.basic
import data.real.basic
import data.real.irrational



lemma lem (m n : ℕ) : 2 * m^2 = n^2 → 2 ∣ n :=
begin
  intros eq₁,
  have : 2 ∣ n^2, by { use m^2, exact eq.symm eq₁},
  exact nat.prime.dvd_of_dvd_pow nat.prime_two ‹2 ∣ n^2 ›,
end



example (a b c : ℕ) (ha : 0 < a) :
a * b = a * c ↔ b = c :=
begin 
exact nat.mul_right_inj ha,
end



lemma wlog_gcd : 
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
    

  have eq₂: 2 ∣ p := lem q p h,

  have eq₂' := eq₂,

  cases eq₂ with p₁ eq₂,

  rw eq₂ at h,

  have : 0 < 2, by {simp only [nat.succ_pos']},
  have eq₃: q^2 = 2 * p₁^2,
    {apply (nat.mul_right_inj this).1, ring at *, assumption},

  have eq₄: 2 * p₁^2 = q^2,
    by { exact eq.symm eq₃},

  have eq₅: 2 ∣ q,
    by exact lem p₁ q eq₄,

  have eq₆: 2 ∣ 1,
    begin
    suffices : 2 ∣ p.gcd q,
    rw coprime_pq at this,
    assumption,
    exact nat.dvd_gcd eq₂' eq₅,
    end,

  rw nat.dvd_one at eq₆,

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