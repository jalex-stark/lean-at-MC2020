import tactic

-- https://www.math.purdue.edu/pow/problem/2017/spring/46

-- Let f:ℕ→ℕ be a function such that f(1)=1 and
-- f(n)=n−f(f(n−1)),n≥2.
-- Show that f(n+f(n))=n for each positive integer n.


lemma arithmetic1 (d : ℕ) (h1 : d ≠ 2) (h2 : 2 ≤ d) : 3 ≤ d := by omega

lemma arithmetic2 { k d : ℕ} (h : k ≤ d - 1) (hd : 2 ≤ d): 1 ≤ d - k := by omega

example (a b c : ℕ) : a = b + c → a - c = b := begin

end

#check nat.sub_eq_of_eq_add
theorem purdue_2017_46 
  (f : ℕ → ℕ) 
  (h1 : f 1 = 1)
  (hf : ∀ n, 2 ≤ n → n = f n + f(f(n-1)) ) :
∀ n, f(n+f(n))=n :=
begin
have hf' : ∀ n, 2 ≤ n → f n = n - f(f(n-1)),
    intros, rw nat.sub_eq_of_eq_add, rw add_comm, exact hf n a,
have hf'' : ∀ n, 2 ≤ n → f (f (n - 1)) = n - f n,
    intros n hn, rw nat.sub_eq_of_eq_add (hf n hn),

have key1 : ∀ n, 2 ≤ n → 1 ≤ f n ∧ f n < n,
  intro n, apply nat.strong_induction_on n,
    intros d hd h1d, 
    by_cases d = 2, {rw [h, h2], norm_num},
      have calc1 : 3 ≤ d := arithmetic1 _ h h1d,
      rw hf', split,
        suffices calc2 : f (f (d - 1)) ≤ d -1, apply arithmetic2; assumption,
        rw hf'', suffices calc3 : 1 ≤ f d,
end

lemma arithmetic3 (a b c : ℤ) : a = b - c ↔ c = b - a := by omega

lemma int_strong_induction_on {p : ℤ → Prop} (n : ℤ) {base : ℤ}
    (hp : ∀ n, (∀ m < n, base ≤ m → p m) → p n) :
base ≤ n → p n :=
begin
  intros hn, 
  have calc1 : ∃ k ≥ 0, n = base + k, use (n - base), split; linarith,
  cases calc1 with k hk, cases hk with k_nonneg hk,
  rw hk at *, clear hk n hn,
  cases k, swap, exfalso, revert k_nonneg, exact (list.mem_nil_iff (p base)).mp,
  apply nat.strong_induction_on k,
  intros n hn, apply hp, intros k hk1 hk2,
  have : ∃ m : ℕ, k = base + m, lift (k - base) to ℕ with m', 
    {use m', rw h, ring}, {linarith},
  cases this with m hm, rw hm, apply hn, 
  rw hm at hk1, 
  simp only [int.of_nat_eq_coe, int.coe_nat_lt, add_lt_add_iff_left] at hk1,
  exact hk1,
end

theorem purdue_2017_46'
  (f : ℤ → ℤ)
  (f_nonneg : ∀ n, 0 ≤ f n) 
  (h1 : f 1 = 1)
  (hf : ∀ n, 2 ≤ n → n = f n + f(f(n-1)) ) :
∀ n, 0≤ n → f(n+f(n))=n :=
begin
have hf' : ∀ n, 2 ≤ n → f n = n - f(f(n-1)),
  intros, rw sub_eq_of_eq_add, apply hf, assumption,
have hf'' : ∀ n, 2 ≤ n → f (f (n - 1)) = n - f n,
  intro, rw arithmetic3, apply hf',


have h2 : f 2 = 1,
    {rw hf' 2, norm_num, rw [h1, h1], norm_num, refl,},

have key1 : ∀ n, 2 ≤ n → 1 ≤ f n ∧ f n < n,
  intros n hn, cases n, 
    swap, exfalso, revert hn, rw imp_false, exact of_to_bool_ff rfl,
  by_cases n = 2, rw h, 
    simp only [int.coe_nat_zero, int.coe_nat_succ, int.of_nat_eq_coe, zero_add],
    norm_num, rw h2, norm_num,
--   revert hn, 
  apply int_strong_induction_on n,
    intros k hk two_le, split,

end
#check int_strong_induction_on 2