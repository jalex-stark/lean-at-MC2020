.. _day2:

***********************
Inductive types
***********************



Natural numbers in Lean 
=======================

The following axioms are the axioms isolated by Peano which uniquely characterize
the natural numbers.

* a term ``0 : mynat``, interpreted as the number zero.
* a function ``succ : mynat → mynat``, with ``succ n`` interpreted as "the number after ``n``".
* The principle of mathematical induction:
  if ``P(0)`` is true and for every natural number ``d`` we know that ``P(d) → P(succ d)``, then ``P(n)`` must be true for every natural number ``n``.


The first axiom says that ``0`` is a natural number. The second says that there
is a ``succ`` function which eats a number and spits out the number after it,
so ``succ 0 = 1``, ``succ 1 = 2`` and so on.

Peano's insights were firstly that these axioms completely characterise
the natural numbers, and secondly that these axioms alone can be used to build
a whole bunch of other structure on the natural numbers, for example
addition, multiplication and so on.




.. /- Lemma : no-side-bar
.. If $\operatorname{succ}(a) = b$, then
.. $$\operatorname{succ}(\operatorname{succ}(a)) = \operatorname{succ}(b).$$
.. -/

.. code:: lean 

  lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
  begin 
    sorry,
  end


Reflexivity (refl) tactic
----------------------------

Let's start with the ``refl`` tactic. ``refl`` stands for "reflexivity", which is a fancy
way of saying that it will prove any goal of the form ``A = A``. It doesn't matter how
complicated ``A`` is, all that matters is that the left hand side is *exactly equal* to the
right hand side (a computer scientist would say "definitionally equal"). 
For example, ``x * y + z = x * y + z`` can be proved by ``refl``, but ``x + y = y + x`` cannot.

Remember that the goal is
the thing with the weird ⊢ thing just before it. The goal in this case is ``x * y + z = x * y + z``,
where ``x``, ``y`` and ``z`` are some of your very own natural numbers.
That's a pretty easy goal to prove -- you can just prove it with the ``refl`` tactic.
Where it used to say ``sorry``, write

.. code-block:: 

    refl,
    
**and don't forget the comma**. Then hit enter to go onto the next line.
If all is well, Lean should tell you "Proof complete!" in the top right box, and there
should be no errors in the bottom right box. 

.. code-block:: lean

    lemma example1 (x y z : ℕ) : x * y + z = x * y + z :=
    begin 
      sorry,
    end

Library_search tactic 
---------------------

Norm_num tactic 
---------------

Simp tactic 
-----------

Have tactic 
------------ 

Set tactic 
-----------


Integers in Lean 
================


norm_cast tactic 
----------------




Exercises
================

Summing by induction
--------------------
.. code:: lean 
   :name: summing_by_induction

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
  :name: interval_cases

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
    :name: odds_and_evens

    #check @nat.even_add
    -- tauto
    lemma even_of_odd_add_odd
      {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
    nat.even (a + b) :=
    begin
      sorry
    end



First, informally prove the following:
If p and q are consecutive primes, then p + q can be written as a product of three factors, each greater than 1.

Then, fill in the following formal sketch of the same theorem. 
We give two lemmas, together with an incomplete proof containing five ``sorry``. 
You can work on the lemmas and ``sorry`` in any order, without affecting the global structure of the proof.
If you like, you can tear down the provided sketch and make your own proof. 

In particular, feel free to solve the last one even if your proofs of the previous two have sorry

.. code-block:: lean
  :name: eq_2_of_even_prime

  example (p : ℕ) : p.prime → p = 2 ∨ p % 2 = 1 :=
  begin
    library_search,
  end

  #check @nat.prime.eq_two_or_odd
  lemma eq_2_of_even_prime {p : ℕ} (hp : nat.prime p) (h_even : nat.even p) : p = 2 :=
  begin
    cases nat.prime.eq_two_or_odd hp, {assumption},
    rw ← nat.not_even_iff at h, contradiction,
  end

.. code-block:: lean
  :name: nontrivial_product_of_not_prime

  -- norm_num, linarith
  lemma nontrivial_product_of_not_prime
    {k : ℕ} (hk : ¬ k.prime) (two_le_k : 2 ≤ k) :
  ∃ a b < k, 1 < a ∧ 1 < b ∧ a * b = k :=
  begin
    have h1 := nat.exists_dvd_of_not_prime2 two_le_k hk,
    rcases h1 with ⟨a, ⟨b, hb⟩, ha1, ha2⟩,
    use [a, b], norm_num, 
    split, assumption,
    split, rw [hb, lt_mul_iff_one_lt_left], linarith, 
    cases b, {linarith}, {simp},
    split, linarith,
    split, rw hb at ha2, apply one_lt_of_nontrivial_factor ha2,
    rw hb,
  end

.. code-block:: lean
  :name: nontrivial_product_of_not_prime_2

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