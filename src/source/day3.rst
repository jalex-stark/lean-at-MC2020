.. _day3:

***********************
Infinitely Many Primes
***********************

.. todo:: 

  Proof-read this file, clean the language and fix any typos.

Today we will prove that there are infinitely many primes using `mathlib library <https://leanprover-community.github.io/mathlib_docs/>`__. Our focus will be on how to *use* the library to prove more complicated theorems. Remember to always **save your work**.

Equality 
===========
So far we have not seen how to deal with propositions of the form ``P = Q``, for example, ``1 + 2 + ... + n = n(n + 1)/2``. Proving these propositions by hand requires messing around with the axioms of type theory.
The standard trick is to make the LHS (almost) equal or to the RHS and then use one of the simplifiers (``norm_num``, ``ring``, ``linarith``, or ``simp``) to close the goal. *Using* equalities on the other hand is very easy. The rewrite tactic (usually shortened to ``rw``) let's you replace the left hand side of an equality with the right hand side.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then 

        ``rw f,`` searches for ``P`` in the target and replaces it with ``Q``.

        ``rw ←f,`` searches for ``Q`` in the target and replaces it with ``P``.
      
      Additionally, if ``hr : R`` is a hypothesis, then 

        ``rw f at hr,`` searches for ``P`` in the expression ``R`` and replaces it with ``Q``.

        ``rw ←f at hr,`` searches for ``Q`` in the expression ``R`` and replaces it with ``P``.

      Mathematically, this is saying "because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around)".

To get the left arrow, type ``\l`` followed by tab. 

.. code:: lean 

  import tactic data.nat.basic
  open nat 

  /--------------------------------------------------------------------------

    ``rw``
      
      If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then 
      ``rw f`` replaces ``P`` with ``Q`` in the target.
      Other variants:
        ``rw f at hp``, ``rw ←f``, ``rw ←f at hr``.

    Delete the ``sorry,`` below and replace them with a legitimate proof.

    --------------------------------------------------------------------------/

  theorem add_self_self_eq_double 
    (x : ℕ) 
  : x + x = 2 * x := 
  begin 
    ring,
  end 

  /-
  For the following problem, use 
    mul_comm a b : a * b = b * a 
  -/

  example (a b c d : ℕ)
    (hyp : c = d * a + b)
    (hyp' : b = a * d)
  : c = 2 * (a * d) :=
  begin
    sorry,
  end

  /-
  For the following problem, use 
    sub_self (x : ℕ) : x - x = 0
  -/

  example (a b c d : ℕ)
    (hyp : c = b * a - d)
    (hyp' : d = a * b)
  : c = 0 :=
  begin
    sorry,
  end


Surjective functions
----------------------
Recall that a function ``f : X → Y`` is surjective if for every ``y : Y`` there exists a term ``x : X``
such that ``f(x) = y``. 
In type theory, for every function ``f`` we can define a corresponding proposition 
``surjective (f) := ∀ y, ∃ x, f x = y`` and a function being surjective is equivalent to saying that the proposition ``surjective(f)`` is inhabited.

.. code:: lean 

  import tactic 
  open function

  /--------------------------------------------------------------------------

  ``unfold``

    If it gets hard to keep track of the definition of ``surjective``, 
    you can use ``unfold surjective,`` or ``unfold surjective at h,`` 
    to get rid of it.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  variables X Y Z : Type
  variables (f : X → Y) (g : Y → Z)

  /-
  surjective (f : X → Y) := ∀ y, ∃ x, f x = y
  -/

  example 
    (hf : surjective f) 
    (hg : surjective g) 
    : surjective (g ∘ f) :=
  begin
    sorry,
  end

  example 
    (hgf : surjective (g ∘ f)) 
    : surjective g :=
  begin
    sorry,
  end


Creating subgoals
===================
Often when we write a long proof in math, we break it up into simpler problems.
This is done in Lean using the ``have`` tactic. 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - ``have hp : P,`` creates a new goal with target ``P`` and 
      adds ``hp : P`` as a hypothesis to the original goal.

The use of ``have`` that we have already seen is related to this one. 
When you use the tactic ``have hq := f(hp),``
Lean is internally replacing it with ``have hq : Q, exact f(hp),``.

``have`` is crucial for being able to use theorems from the library.
To use these theorems you have to create terms that match the hypothesis *exactly*.
Consider the following example. 
The type ``n > 0`` is not the same as ``0 < n``.
If you need a term of type ``n > 0`` and you only have ``hn : 0 < n``, then you can use
``have hn2 : n > 0, linarith,`` and you will have constructed a term ``hn2`` of type ``n > 0``.


We will need the following lemma later. Remember to save your proof. 
(Here's a :doc:`hint <../hint_1_have_exercise>` if you need one.)
**Warning:** If you need to type the divisibility symbol, type ``\mid``. 
This is **not** the vertical line on your keyboard.

.. code:: lean 

  import tactic data.nat.prime
  open nat

  /--------------------------------------------------------------------------

  ``have``

    ``have hp : P,`` creates a new goal with target ``P`` and 
    adds ``hp : P`` as a hypothesis to the original goal.

  You'll need the following theorem from the library:

  nat.dvd_sub : n ≤ m → k ∣ m → k ∣ n → k ∣ m - n
  
     (Note that you don't need to provide n m k as inputs to dvd_sub
     Lean can infer these from the rest of the expression.
     More on this tomorrow.)

  Delete the ``sorry,`` below and replace it with a legitimate proof.

  --------------------------------------------------------------------------/

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) :=
  begin
    sorry,
  end


Infinitely many primes 
=======================

We'll now prove that there are infinitely many primes. 
The strategy is to show that there is a prime greater than ``n``, for every natural number ``n``.
We will choose this prime to be smallest non-trivial factor of ``n! + 1``. 
We'll need the following definitions and theorems from the library.

**Primes** 
  * ``m ∣ n := ∃ k : ℕ, m = n * k``
  * ``m.prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)``
  * ``prime.not_dvd_one : (prime p) → ¬ p ∣ 1``

**Factorials**
  * ``n.fact := n!  --n factorial``
  * ``fact_pos : ∀ (n : ℕ), 0 < n.fact``
  * ``dvd_fact : 0 < m → m ≤ n → m ∣ n.fact``

**Smallest factor** 
  * ``n.min_fac :=`` smallest non-trivial factor of ``n``
  * ``min_fac_prime : n ≠ 1 → n.min_fac.prime`` 
  * ``min_fac_pos : ∀ (n : ℕ), 0 < n.min_fac``
  * ``min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n``

Check out `data.nat.prime <https://leanprover-community.github.io/mathlib_docs/data/nat/prime.html>`__ for more theorems about primes.
The exercise below is very open-ended.
You should take your time, check the goal window at every step, and sketch out the proof on paper whenever you get lost.

.. code:: lean 

  import tactic data.nat.prime
  noncomputable theory
  open_locale classical

  open nat

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1) :=
  begin
    sorry,
  end

  /-
  dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → (p ∣ 1)

  m ∣ n := ∃ k : ℕ, m = n * k
  m.prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)
  prime.not_dvd_one : (prime p) → ¬ p ∣ 1

  n.fact := n! (n factorial)
  fact_pos : ∀ (n : ℕ), 0 < n.fact
  dvd_fact : 0 < m → m ≤ n → m ∣ n.fact

  n.min_fac := smallest non-trivial factor of n
  min_fac_prime : n ≠ 1 → n.min_fac.prime
  min_fac_pos : ∀ (n : ℕ), 0 < n.min_fac
  min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n
  -/

  theorem exists_infinite_primes (n : ℕ) : ∃ p, nat.prime p ∧ p ≥ n :=
  begin
    set p:= (n.fact + 1).min_fac,
    sorry,
  end


Final remarks 
=================
It would be great if there was a one-to-one correspondence between "hand-written proofs" and proofs in Lean. But that is far from the case. When we write proofs we leave out a lot of details without even realizing it and expect the reader to be intelligent enough to fill them in. This is both a bug and feature. On the one hand this makes proofs readable. On the other hand too many "obviously true" arguments make proofs undecipherable and often wrong.

Unlike human readers, computers are pretty dumb (as of writing these notes). They can only do what you tell them to do and you cannot expect them to "fill in the details". But it is humanly impossible to teach a computer every single trivial fact about, say the natural numbers. The `Lean math library <https://leanprover-community.github.io/mathlib_docs/>`__ contains a lot of trivial theorems but this collection is far from comprehensive.
So theorem proving is Lean often involves the following steps:

* Scan the library to see which definitions and theorems might be useful.

* Choose the right hypotheses and wording for your theorem to match the theorems in the library. (Sadly, changing the wording slightly might end up making the proof infinitely harder to prove.)

* Break the theorem into small lemmas so that you can use the simplifiers more frequently.

The hope is that one day we won’t have to do this and a theorem proving AI will eliminate the difference between human proofs and machine proofs.