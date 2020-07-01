.. _day4:

***************************
Infinitude of primes
***************************

The way we will prove that there are infinitely many primes is by showing that 
**for every natural number n, the smallest prime factor of (n! + 1) is greater than n**.
The steps will be following:

1. We'll let ``p`` be the smallest factor of ``n! + 1`` that is bigger than 1.
2. We'll show that ``p`` is a prime.
3. Next we'll show that ``p > n``.  This is a proof by contradiction. 

  4. Suppose on the contrary that ``p ≤ n``.
  5. This implies that ``p`` divides ``n!``.
  6. As ``p`` divides ``n!`` and ``n! + 1``, ``p`` divides 1.
  7. This is a contradiction.



.. * - ``have``
..     - The tactic ``have hp : P,`` adds the hypothesis ``hp : P`` to the current goal 
..       and opens a new subgoal with target ``⊢ P``. 
      
..       Mathematically, this is like introducing an intermediate claim.


In Lean, division is defined as ``p | a`` is defined as ``∃ k : ℕ, a = p * k``.


..code::

    #eval nat.min_fac 51 -- smallest divisor of n that is greater than 1, unless n = 1
    #eval nat.fact 5  -- n factorial

    #check nat.min_fac_prime -- smallest divisor of n is prime
    #check nat.min_fac_pos -- smallest divisor of n is positive
    #check nat.min_fac_dvd -- smallest divisor of n divides n

    #check nat.fact_pos -- n factorial is always > 0
    #check nat.dvd_fact -- n divides n factorial

    #check nat.dvd_one 
    #check nat.dvd_sub

    #print nat.prime
    /-
    infinitude_of_primes.lean:31:0: information print result
    def nat.prime (p : ℕ): ℕ → Prop :=
      2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p
    -/

1.

.. code:: lean 
  :name: dvd_sub

  import tactic data.nat.prime

  #check @nat.dvd_sub
  /- nat.dvd_sub : ∀ {k m n : ℕ}, n ≤ m → k ∣ m → k ∣ n → k ∣ m - n -/


  theorem dvd_sub' (p a b : ℕ) : (p ∣ a + b) → (p ∣ a) → (p ∣ b) :=
  begin
    have H : a ≤ a + b, {simp, },
    have K : (a + b) - a = b, {simp,},
    have := (@nat.dvd_sub p (a + b) a H),
    rw K at this,
    tauto,
  end

  lemma prime_ge_2 (p:nat) (pp: p.prime) : 2 ≤ p :=
  begin
    cases pp,
    exact pp_left,
  end

  lemma prime_not_dvd_one_aux (p:nat) (pp: 2 ≤ p) : ¬ p ∣ 1 :=
  begin
    contrapose! pp,
    have := @nat.dvd_one p,
    rw this at pp,
    linarith,
  end

  lemma prime_not_dvd_one (p:nat) (pp: nat.prime p) : ¬ p ∣ 1 :=
  begin
    apply prime_not_dvd_one_aux,
    exact prime_ge_2 p pp,
  end

  theorem exists_infinite_primes (n : ℕ) : ∃ p, nat.prime p ∧ p ≥ n :=
  begin
    set p:= nat.min_fac (n.fact + 1), use p,
    have key1 : p ∣ n.fact + 1, by exact nat.min_fac_dvd (n.fact + 1),
    have pp: nat.prime p,
    {
      apply nat.min_fac_prime,
      have := nat.fact_pos n,
      linarith,
    },
    split, assumption,
    {
      by_contradiction,
      push_neg at a,
      have key2 : p ∣ n.fact, apply nat.dvd_fact,
      exact nat.min_fac_pos (n.fact + 1),
      linarith,
      have := dvd_sub' p n.fact 1 key1 key2,
      exact prime_not_dvd_one p pp this, -- can get rid of this
    },
  end


