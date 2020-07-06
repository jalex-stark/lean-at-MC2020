.. _day2:

***************************
Mathematics in Lean
***************************

Lean's `mathlib library <https://leanprover-community.github.io/mathlib_docs/>`__ contains several standard axioms, definitions, theorems, and proofs from which one can to build more complicated math.
We will focus on how to *use* these to prove more complicated theorems and later on go deeper into some of the definitions.
We will almost exclusively focus on theorems about natural numbers.

Currying 
==============

There is no difference between functions and implications in type theory. 
And products for arbitrary types behave exactly like "∧" for propositions.
This is a both bug and a feature.

.. code:: lean 
  :name: curry_uncurry

  theorem curry (P Q R : Type) (f : P × Q → R) : P → (Q → R) := 
  begin 
    sorry,
  end 
  
  theorem uncurry (P Q R : Type) (f : P → (Q → R)) : P × Q → R := 
  begin 
    sorry,
  end

These two theorems together imply that a function ``P × Q → R`` is equivalent to a function ``P → (Q → R)``.
This is called **currying** (named Haskell Curry).
Internally, Lean will always curry functions. You will never see a function defined from a product to another type.
Lean will also drop the brackets so that ``P → Q → R → S`` is the same as ``P → (Q → (R → S)))``.


Consider a function ``f : P → Q → R → S`` and elements ``hp : P``, ``hq : Q``, ``hr : R``.
Then 
``f(hp)`` is of type ``Q → R → S``, ``((f (hp)) hq)`` is of type ``R → S``, and ``(((f (hp)) hq) hr)`` is of type ``S``.
This is looking less and less fun.
Lean allows you to skip the brackets completely. So that 
``f hp`` is of type ``Q → R → S``, ``f hp hq`` is of type ``R → S``, and ``f hp hq hr`` is of type ``S``.

.. topic:: Brackets in Lean 

  * The type ``P → Q → R → S`` is the same as ``P → (Q → (R → S)))``.
  * The element ``f hp hq hr`` is the same as ``(((f (hp)) hq) hr)``.


Quantifiers 
============== 


In type theory, a proposition ``(∀ x : X, P x)`` is just a function ``X → Prop`` which sends ``x : X`` to ``P x``.
The tactics for dealing with ``∀`` are hence exactly ones as for ``→``.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - If ``hp : (∃ x : X, P x)`` is a hypothesis, then 
      ``cases hp with x key,`` breaks it into ``x : X`` and ``key : P x``.

  * - ``use``
    - If the target of the current goal is ``⊢ ∃ x : X, P x`` 
      and ``y : X,`` is a hypothesis, then 
      ``use y,`` changes the target to ``⊢ P y`` and tries to close the goal.

something here.

1. **Lounge paradox**
  
  There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game. 
  (See :doc:`hint <../hint_day1_lounge_paradox1>` ).

  .. code:: lean
    :name: lounge_paradox

      import tactic
      -- the next two lines let us use the by_cases tactic without trouble
      noncomputable theory
      open_locale classical

      --BEGIN--
      theorem lounge 
        (camper : Type) 
        (playing : camper → Prop) 
        (alice : camper) -- making sure that there is at least one camper in the lounge
        : ∃ x, (playing x → ∀ y, playing y) :=
      begin
        by_cases h : ∃ bob, ¬ playing bob,
        cases h with bob,
        use bob,

        push_neg at h,
        use alice,
        intro ,
        exact h,
      end
      --END--

2. **Barber paradox**
  

  Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:

  .. code-block:: lean

    import tactic
    -- the next two lines let us use the by_cases tactic without trouble
    noncomputable theory
    open_locale classical

    --BEGIN--
    variables (men : Type) (barber : men) 
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : 
      false := 
      begin 

      end 
    --END--


3.  **Surjective functions** 

  .. code:: lean 

    import tactic 
    open function

    -- In the remaining of this file, f and g will denote functions from
    -- ℕ to ℕ.
    variables (f g : ℕ → ℕ)

    /-
    surjective (f : X → Y) := ∀ y, ∃ x, f x = y
    -/

    example (h : surjective (g ∘ f)) : surjective g :=
    begin
      sorry,
    end

    example (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
    begin
      sorry,
    end

  




Proving "trivial" statements 
=============================


In mathlib, divisibility for natural numbers is defined as a *proposition* follows.

.. code:: 

  a ∣ b := (∃ k : ℕ, a = b * k)

For example, ``2 | 4`` will be a proposition ``∃ k : ℕ, 4 = 2 * k``. 
**Very important.** And so ``2 | 4`` is not saying that "2 divides 4 *is true*". 
It is simply a proposition that requires a proof. 

Similarly, the mathlib library also contains the following definition of ``prime``.

.. code:: 

    def nat.prime (p : ℕ) : Prop 
    := 
      2 ≤ p                                       -- p is at least 2
      ∧                                           -- and 
      ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p            -- if m divides p, then m = 1 or m = p.

This time ``nat.prime`` itself is not a proposition but for every natural number ``n``, 
``nat.prime n`` is a *proposition*. 
So that ``nat.prime 2`` requires a proof.
Fortunately, there are pre-made tactics in Lean for providing such trivial proofs.


.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``norm_num``
    - ``norm_num`` is Lean’s calculator. If the target has a proof that involves *only* numbers and arithmetic operations,
      then ``norm_num`` will close this goal.

      If ``hp : P`` is an assumption then ``norm_num at hp,`` tries to use simplify ``hp`` using basic arithmetic operations.

  * - ``ring`` 
    - ``ring,`` is the symbolic manipulator of Lean. 
      If the target has a proof that involves *only* algebraic operations, 
      then ``ring,`` will close the goal.

      If ``hp : P`` is an assumption then ``ring at hp,`` tries to use simplify ``hp`` using basic algebraic operations.

  * - ``linarith`` 
    - ``linarith,`` is Lean's inequality solver.
  
  * - ``simp`` 
    - ``simp,`` is a very complex tactic that tries to use theorems from the mathlib library to close the goal. 
      You should only ever use ``simp,`` to close a goal because its behavior changes as more theorems get added to the library.

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

  example (m a b : ℕ) :  m^2 + (a + b) * m + a * b = (m + a) * (m + b) :=
  begin
    sorry,
  end

  example : 101 ∣ 2020 :=
  begin
    sorry,
  end


  #print nat.prime 
  example : nat.prime 101 := 
  begin 
    sorry,
  end

  -- recall that a ∣ b := (∃ k : ℕ, a = b * k)
  example (m a b : ℕ) :  m + a ∣ m^2 + (a + b) * m + a * b :=
  begin
    sorry,
  end

  example (p : ℕ) : nat.prime p → ¬ (p = 1) :=
  begin 
    sorry,
  end 


Rewriting 
===========
The final two tactics we need before we can start doing some interesting math is ``rw,`` (for rewrite). 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f : P = Q`` (or ``f : P ↔ Q``) is a hypothesis, then 

        ``rw f,`` searches for ``P`` in the target and replaces the first instance it finds with ``Q``.

        ``rw ←f,`` searches for ``Q`` in the target and replaces the first instance it finds with ``P``.
      
      If ``hr : R`` is another hypothesis, then 

        ``rw f at hr,`` searches for ``P`` in the ``R`` and replaces the first instance it finds with ``Q``.

        ``rw ←f at hr,`` searches for ``Q`` in the ``R`` and replaces the first instance it finds with ``P``.

      Mathematically, this is saying because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around).

.. code:: lean 

  import tactic data.nat.basic 

  #check nat.add_comm 

  example (a b : ℕ) (f : ℕ → ℕ) : f(a + b) = f(b + a) :=
  begin 
    rw nat.add_comm,
  end 

  example (a b c : ℕ) (f : ℕ → ℕ) :  c + f(a + b) = f(b + a) + c :=
  begin 
    rw nat.add_comm a b,
  end  

.. In the following exercises, we will use the following two lemmas:
..   mul_assoc a b c : a * b * c = a * (b * c)
..   mul_comm a b : a*b = b*a
.. Hence the command 
..   rw mul_assoc a b c,
.. will replace a*b*c by a*(b*c) in the current goal.
.. In order to replace backward, we use
..   rw ← mul_assoc a b c,
.. replacing a*(b*c) by a*b*c in the current goal.
.. Of course we don't want to constantly invoke those lemmas, and we will eventually introduce
.. more powerful solutions.
.. -/

.. example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
.. begin
..   rw mul_comm a b,
..   rw mul_assoc b a c,
.. end

.. -- 0001
.. example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
.. begin
..   sorry
.. end

.. -- 0002
.. example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
.. begin
..   sorry
.. end

.. /-
.. Now let's return to the preceding example to experiment with what happens
.. if we don't give arguments to mul_assoc or mul_comm.
.. For instance, you can start the next proof with
..   rw ← mul_assoc,
.. Try to figure out what happens.
.. -/

.. -- 0003
.. example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
.. begin
..   sorry
.. end

.. /-
.. We can also perform rewriting in an assumption of the local context, using for instance
..   rw mul_comm a b at hyp,
.. in order to replace a*b by b*a in assumption hyp.
.. The next example will use a third lemma:
..   two_mul a : 2*a = a + a
.. Also we use the `exact` tactic, which allows to provide a direct proof term.
.. -/

.. example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
.. begin
..   rw hyp' at hyp,
..   rw mul_comm d a at hyp,
..   rw ← two_mul (a*d) at hyp,
..   rw ← mul_assoc 2 a d at hyp,
..   exact hyp, -- Our assumption hyp is now exactly what we have to prove
.. end

.. /-
.. And the next one can use:
..   sub_self x : x - x = 0
.. -/

.. -- 0004
.. example (a b c d : ℝ) (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 :=
.. begin
..   sorry
.. end

Mathematical Induction 
========================


.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``induction``
    - If ``n : ℕ`` is a hypothesis and the target of the current goal is a proposition 
      ``⊢ P(n)`` that depends on ``n``,  
      then ``induction n with d hd,`` removes the hypothesis ``n : ℕ`` produces breaks down the current goal into two goals:
      
      * the first with target ``⊢ P(0)`` 
      * the second with two added hypotheses ``d : ℕ`` and ``hd : P(d)`` and target ``⊢ P(d.succ)``.

      This is precisely the statement of mathematical induction. 


.. code:: lean 

  def f : ℕ → ℕ
  | 0 := 0
  | (n + 1) := n + 1 + f n

  example : f 1 = 1 := 
  begin
    unfold f,
  end

  example (n : ℕ) : 2 * f n = n * (n + 1) :=
  begin
    induction n with d hd,  
    -- base case
    { unfold f, simp },
    rw nat.succ_eq_add_one,
    unfold f, ring, 
    rw hd, ring,
  end

.. todo:: 

  Add a few fun problems on induction.