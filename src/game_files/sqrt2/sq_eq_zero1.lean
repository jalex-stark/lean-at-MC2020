import tactic
import data.nat.basic
-- Level name : squares_to_zero

/-
Comment here
-/

/- Hint : title_of_the_hint
Content of the hint
-/

/- Tactic : ring
Normalizes expressions in commutative rings by applying lots of 
distributivity, associativity, commutativity. Can prove equalities.
-/

example := nat.pow_two

/- Axiom : nat.pow_two
statement_of_the_axiom
-/

lemma eq_zero_of_sq_eq_zero (m : ℕ) (hm : m^2 = 0) : m = 0 :=
begin
  simp only [nat.pow_two] at hm, 
  simp only [nat.mul_eq_zero, or_self] at hm,
  assumption,
end

