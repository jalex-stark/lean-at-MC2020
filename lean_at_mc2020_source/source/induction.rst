.. _induction:

***********************
Natural numbers in Lean
***********************





Exercises
================

Summing by induction
--------------------
.. code:: lean 

    -- by landing in ℤ, we avoid the perils of nat subtraction
    def f : ℕ → ℤ
    | 0 := 0
    | (n + 1) := n + f n

    example : f 1 = 1 := by refl

    -- ring, norm_num, push_cast, norm_cast
    -- nat.succ_eq_add_one
    example (n : ℕ) : 2 * f n = n * (n - 1) :=
    begin
      induction n with d hd, 
      -- n = 0 base case
      { sorry }, 
      -- inductive step
      sorry
    end




Meet interval_cases
-------------------

interval_cases can reduce the problem to check the cases c = 0 and c = 1. 

.. code:: lean 

  lemma one_lt_of_nontrivial_factor 
    {b c : ℕ} (hb : b < b * c) :
  1 < c :=
  begin
    contrapose! hb, 
    interval_cases c,
    sorry
  end


Odds and evens
---------------
.. code:: lean 

    #check @nat.even_add
    -- tauto
    lemma even_of_odd_add_odd
      {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
    nat.even (a + b) :=
    begin
      sorry
    end


.. code-block:: lean

  lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
  begin
    cases nat.prime.eq_two_or_odd hp, {assumption},
    rw ← nat.not_even_iff at h, contradiction,
  end

