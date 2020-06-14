import data.fintype.basic
import data.nat.prime
import group_theory.order_of_element
import tactic
import data.int.modeq
import data.zmod.basic

noncomputable theory
open_locale classical
variables {G : Type*} [group G]

lemma mul_comm_of_cyclic (g : G) (cyclic : ∀ x, ∃ n : ℤ, x = g^n) :
∀ a b : G, a * b = b * a :=
begin
  intros a b, 
  cases cyclic a with na hna,
  cases cyclic b with nb hnb,
  rw [hna, hnb], 
  repeat { rw ← gpow_add },
  rw add_comm,
end

example : 0 < 4 := by norm_num

lemma mul_comm_of_exponent_two (g : G) (exponent_two : ∀ x, x^2 = 1) :
∀ a b : G, a * b = b * a :=
begin
  intros a b,
end

lemma factors_of_4 {n : ℕ} (h4 : n ≠ 4) (hn : n ∣ 4) : n = 1 ∨ n = 2 :=
begin
  have := nat.le_of_dvd (by norm_num) hn,
  interval_cases n, 
    -- n = 0
    {cases hn with _ h, norm_num at h},
    -- n = 1
    { tauto },
    -- n = 2
    { tauto },
    -- n = 3 
    exfalso, cases hn with k hk, revert hk, 
    omega,
end

example 

/-- Every group of order 4 is commutative -/
lemma mul_comm_of_card_eq_four (G : Type*) [fintype G] [group G] (hG4 : fintype.card G = 4) :
∀ g h : G, g * h = h * g := 
begin
  by_cases ∃ (x : G), order_of x = 4,
  cases h with x hx, apply mul_comm_of_cyclic x,
  have := is_cyclic_of_order_of_eq_card x,
end


lemma sq_mod_8 (x : zmod 8) : x ^ 2 = 0 ∨ x^2 = 1 :=
begin
  cases x with x x_lt,
  have := nat.le_of_lt_succ x_lt,
  interval_cases x, -- why doesn't this work
end
