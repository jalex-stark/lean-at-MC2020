.. _day2:

***********************
Natural numbers in Lean
***********************

Today, we will start manipulating natural numbers in Lean. 
Lean's `mathlib library <https://leanprover-community.github.io/mathlib_docs/>`__ contains several standard axioms, definitions, theorems, and proofs from which one can to build more complicated math.
We will focus on how to *use* these to prove more complicated theorems and later on go deeper into some of the definitions.

.. For now, we just need the fact that the natural numbers are defined as the type``0, 0.succ, 0.succ.succ, 0.succ.succ.succ, ...`` and then we add some pretty symbols ``1 := 0.succ``, ``2 := 0.succ.succ``, and so on.

Equality 
============

.. table::
  :widths: 40, 60

  +--------------------+-------------------------------------------------------+
  | ``refl``           | Closes the current goal if the target is ``⊢ P = P``. |
  +--------------------+-------------------------------------------------------+
  | ``symmetry``       | If the target of the current goal is                  |
  |                    | ``⊢ P = Q`` then                                      |
  |                    | ``symmetry,``                                         |
  |                    | changes it to                                         |
  |                    | ``⊢ Q = P``.                                          |
  +--------------------+-------------------------------------------------------+
  | ``symmetry at hf`` | If                                                    |
  |                    | ``hf : P = Q``                                        |
  |                    | is a hypothesis in the current goal, then             |
  |                    | ``symmetry at hf,``                                   |
  |                    | changes it to                                         |
  |                    | ``hf : Q = P``.                                       |
  +--------------------+-------------------------------------------------------+
  | ``rw hf``          | If                                                    |
  |                    | ``hf : P = Q``                                        |
  |                    | is a hypothesis in the current goal, then             |
  |                    | ``rw hf,``                                            |
  |                    | replaces the first occurrence of                      |
  |                    | ``P``                                                 |
  |                    | in the target with                                    |
  |                    | ``Q``.                                                |
  +--------------------+-------------------------------------------------------+
  | ``rw hf at hp``    | If                                                    |
  |                    | ``hf : P = Q``                                        |
  |                    | and                                                   |
  |                    | ``hp : R``                                            |
  |                    | are hypotheses in the current goal, then              |
  |                    | ``rw hf at hp,``                                      |
  |                    | replaces the first occurrence of                      |
  |                    | ``P``                                                 |
  |                    | in                                                    |
  |                    | ``R``                                                 |
  |                    | with                                                  |
  |                    | ``Q``.                                                |
  +--------------------+-------------------------------------------------------+

Creating subgoals  
==============================


.. table::
  :widths: 30, 70

  +-------------------+---------------------------------------------------------+
  | ``have hp := P,`` | adds the hypothesis                                     |
  |                   | ``hp : P``                                              |
  |                   | to the current goal if                                  |
  |                   | ``hp``                                                  |
  |                   | is a term of type                                       |
  |                   | ``P``.                                                  |
  +-------------------+---------------------------------------------------------+
  | ``have hp : P,``  | Adds the hypothesis                                     |
  |                   | ``hp : P``                                              |
  |                   | to the current goal and opens a new subgoal with target |
  |                   | ``⊢ P``.                                                |
  |                   | The new subgoal becomes the current goal.               |
  +-------------------+---------------------------------------------------------+

Trivial statements
====================

.. table::
  :widths: 20, 80

  +--------------------+---------------------------------------------------------------------------------------+
  | Tactic             | Use                                                                                   |
  +====================+=======================================================================================+
  | ``norm_num``       | ``norm_num`` is Lean's calculator.                                                    |
  |                    | If the goal has a proof that involves no variables but just arithmetic                |
  |                    | and numbers then ``norm_num`` will resolve this goal                                  |
  +--------------------+---------------------------------------------------------------------------------------+
  | ``norm_num at hp`` | If ``hp : P`` is an assumption then ``norm_num at hp``                                |
  |                    | tries to use simplify ``hp`` using just arithmetic                                    |
  +--------------------+---------------------------------------------------------------------------------------+
  | ``ring``           | ``ring`` is a tactic for simplifies basic algebraic operations                        |
  +--------------------+---------------------------------------------------------------------------------------+
  | ``ring at hp``     | If ``hp : P`` is an assumption then ``ring at hp``                                    |
  |                    | tries to use simplify ``hp`` using just algebraic operations                          |
  +--------------------+---------------------------------------------------------------------------------------+
  | ``linarith``       | ``linarith`` can manipulate and close goals involving simple inequalities             |
  +--------------------+---------------------------------------------------------------------------------------+
  | ``simp``           | ``simp`` is a very complex tactic that tries to use theorems from the mathlib library |
  |                    | to close the goal.                                                                    |
  |                    | You should only ever use ``simp`` to close a goal because its behavior                |
  |                    | changes as more theorems get added to the library.                                    |
  +--------------------+---------------------------------------------------------------------------------------+

In the following problems, replace ``sorry`` with ``norm_num``, ``ring``, ``linarith``, ``simp`` and see which of these simplifiers close the goal.

.. code:: lean 

  import tactic data.nat.prime 

  /-
  norm_num,
  ring,
  linarith,
  simp,
  -/

  example (m n : ℕ) : 1 > 0 :=
  begin
    sorry,
  end

  example (m n : ℤ ) :  m^2 - n^2 = (m + n) * (m - n) :=
  begin
    sorry,
  end

  example : 101 ∣ 2020 :=
  begin
    sorry,
  end

  #check nat.prime 
  example : 101.prime := 
  begin 
    sorry,
  end 

Exercises
================

.. Summing by induction
.. --------------------
.. You're going to end up with a goal state that has both nats and ints in it.
.. Use push_cast if you want to think about it as an int statement, and norm_cast if you want to think about it as a nat statement.
.. (Hint: the integers are a ring and the naturals are not.)

.. .. code:: lean 
..   :name: summing_by_induction

..   import tactic
..   import data.int.basic

..   -- by landing in ℤ, we avoid the perils of nat subtraction
..   def f : ℕ → ℤ
..   | 0 := 0
..   | (n + 1) := n + f n

..   example : f 1 = 1 := by refl

..   #check nat.succ_eq_add_one
..   example (n : ℕ) : 2 * f n = n * (n - 1) :=
..   begin
..     induction n with d hd, 
..     -- n = 0 base case
..     { sorry }, 
..     -- inductive step
..     sorry
..   end




Meet interval_cases
-------------------

interval_cases can reduce the problem to check the cases c = 0 and c = 1. 

.. code:: lean 
  :name: interval_cases

  import tactic

  lemma one_lt_of_nontrivial_factor 
    {b c : ℕ} (hb : b < b * c) :
  1 < c :=
  begin
    contrapose! hb, 
    interval_cases c,
    sorry
  end




A number theory puzzle
----------------------
First, informally prove the following:
If p and q are consecutive primes, then p + q can be written as a product of three factors, each greater than 1.

Then, fill in the following formal sketch of the same theorem. 
We give two lemmas, together with an incomplete proof containing five ``sorry``. 
You can work on the lemmas and ``sorry`` in any order, without affecting the global structure of the proof.
If you like, you can tear down the provided sketch and make your own proof. 

In particular, feel free to solve the last one even if your proofs of the previous two have sorry

.. code-block:: lean
   :name: eq_2_of_even_prime

    import tactic
    import data.nat.prime
    import data.nat.parity

    example (p : ℕ) : p.prime → p = 2 ∨ p ≡ 1 [MOD 2] :=
    begin
      library_search!,
    end

    example (p : ℕ) : p ≡ 1 [MOD 2] ↔ ¬ p.even :=
    begin
      library_search!,
    end

    lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
    begin
      sorry
    end


.. code-block:: lean
   :name: nontrivial_product_of_not_prime

    import tactic
    import data.nat.prime
    import data.nat.parity

    -- norm_num, linarith
    lemma nontrivial_product_of_not_prime
      {k : ℕ} (hk : ¬ k.prime) (two_le_k : 2 ≤ k) :
    ∃ a b < k, 1 < a ∧ 1 < b ∧ a * b = k :=
    begin
      have h1 := nat.exists_dvd_of_not_prime2 two_le_k hk,
      rcases h1 with ⟨a, ⟨b, hb⟩, ha1, ha2⟩,
      use [a, b], norm_num, 
      sorry
    end

.. code-block:: lean
   :name: nontrivial_product_of_not_prime_2

    import tactic
    import data.nat.prime
    import data.nat.parity

    lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 := sorry

    lemma nontrivial_product_of_not_prime {k : ℕ} (hk : ¬ k.prime) (two_le_k : 2 ≤ k) :
    ∃ a b < k, 1 < a ∧ 1 < b ∧ a * b = k := sorry

    theorem three_fac_of_sum_consecutive_primes 
    {p q : ℕ} (hp : p.prime) (hq : q.prime) (hpq : p < q) 
    (p_ne_2 : p ≠ 2) (q_ne_2 : q ≠ 2)
    (consecutive : ∀ k, p < k → k < q → ¬ k.prime) :
    ∃ a b c, p + q = a * b * c ∧ a > 1 ∧ b > 1 ∧ c > 1 :=
    begin
      use 2, have h1 : nat.even (p + q), 
      { sorry },

      cases h1 with k hk, 
      have hk' : ¬ k.prime, 
      { sorry },

      have h2k : 2 ≤ k, 
      { sorry },

      have h2 := nat.exists_dvd_of_not_prime2 _ hk',
      swap, 
      { sorry },

      rcases nontrivial_product_of_not_prime hk' h2k with ⟨ b, c, hbk, hck, hb1, hc1, hbc⟩,
      use [b,c],
      { sorry },
    end
