.. _day2:

***************************
Logic in Lean - Part 2
***************************

.. todo:: 

  Proof-read this file, clean the language and fix any typos.


Your mission today is to wrap up the remaining bits of logic and move on to doing some "actual math".
Remember to **always save your work**. 
You might find the :doc:`Glossary of tactics<../tactics>` page and the :doc:`Pretty symbols<../symbols>` page useful.

Before we move on to new stuff, let's understand what we did yesterday. 

Behind the scenes 
==================

**A note on brackets:** 
It is not uncommon to compose half a dozen functions in Lean. 
The brackets get really messy and unwieldy. 
As such, Lean will often drop the brackets by following the following conventions.

* The function ``P → Q → R → S`` stands for ``P → (Q → (R → S))``.
* The expression ``a + b + c + d`` stands for ``((a + b) + c) + d``.

An easy way to remember this is that, arrows are bracketed on the right and binary operators on the left.

Proof irrelevance 
-------------------
It might feel a bit weird to say that a proposition has proofs as its inhabitants. 
Proofs can get huge and it seems unnecessary to have to remember not just the statement but also its proof.
This is something we don't normally do in math.
To hide this complication, in type theory there is an axiom, called *proof irrelevance*, which says that 
if ``P : Prop`` and ``hp1 hp2 : P`` then ``hp1 = hp2``. 
Taking our *analogy* with sets further, you can think of a proposition as a set which is either empty or contains a single element (false or true).
In fact, in some forms of type theory (e.g. `homotopy type theory <https://en.wikipedia.org/wiki/Homotopy_type_theory>`__) this is taken as the definition of propositions.
This is of course not true for general types. 
For example, ``0 : ℕ ≠ 1 : ℕ``. 


Proofs as functions 
--------------------

Every time you successfully construct a proof of a theorem say 

.. code:: 

  theorem tautology (P : Prop) : P → P :=
  begin
    intro hp,
    exact hp,
  end

Lean constructs a *proof term* ``tautology : ∀ P : Prop, P → P`` 
(you can see this by typing ``#check tautology``).

In type theory, the *for all* quantifier, ``∀``, is a generalized function, called a `dependent function <https://en.wikipedia.org/wiki/Dependent_type>`__.
For all practical purposes, we can think of ``tautology`` as having the type ``(P : Prop) → (P → P)``.
Note that this is not a function in the classical sense of the word because the codomain ``(P → P)`` *depends* on the input variable ``P``.
If ``Q : Prop``, then ``tautology(Q)`` is a term of type  ``Q → Q``.

Consider a theorem with multiple hypothesis, say 

.. code::

  theorem hello_world (hp : P) (hq : Q) (hr : R) : S

Once we provide a proof of it, Lean will create a proof term
``hello_world : (hp:P) → (hq:Q) → (hr:R) → S``.
So that if we have terms ``hp' : P``, ``hq' : Q``, ``hr' : R``
then ``hello_world hp' hq' hr'`` (note the convenient lack of brackets) will be a term of type ``S``.


Once constructed, any term can be used in a later proof. For example,

.. code:: 

  example (P Q : Prop) : (P → Q) → (P → Q) :=
  begin
    exact tautology (P → Q),
  end

This is how Lean simulates mathematics.
Every time you prove a theorem using tactics a *proof term* gets created. 
Because of proof irrelevance, Lean forgets the exact content of the proof and 
only remembers its type.
All the proof terms can then be used in later proofs.
All of this falls under the giant umbrella of the `Curry--Howard correspondence <https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`__.

We'll now continue our study of the remaining logical operators: *and* (``∧``), 
*or* (``∨``), 
*if and only if* (``↔``), 
*for all* (``∀``),
*there exists* (``∃``).

And / Or
===============================
The operators *and* (``∧``) and *or* (``∨``) are very easy to use in Lean.
Given a term ``hpq : P ∧ Q``, 
there are tactics that let you 
create terms ``hp : P`` and ``hq : Q``, and vice versa.
Similarly for ``P ∨ Q``, with a subtle change (see below).

**Note** that when multiple goals are open, you are trying to solve the topmost goal.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - ``cases`` is a general tactic that breaks a complicated term into simpler ones.

      If ``hpq`` is a term of type ``P ∧ Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``.

      If ``fg`` is a term of type ``P ↔ Q``, then 
      ``cases fg with f g,`` breaks it into ``f : P → Q`` and ``g : Q → P``.

      If ``hpq`` is a term of type ``P ∨ Q``, then 
      ``cases hpq with hp hq,`` creates two goals and adds the hypotheses ``hp : P`` and ``hq : Q`` to one each.

  * - ``split``
    - ``split`` is a general tactic that breaks a complicated goal into simpler ones.
    
      If the target of the current goal is ``P ∧ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P × Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P ↔ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P → Q`` and ``Q → P``.

  * - ``left``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``left,`` changes the target to ``P``.
  
  * - ``right``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``right,`` changes the target to ``Q``.


.. code:: lean
  :name: and_or_example

  import tactic

  -- these two statements tell Lean to use the law of excluded middle as necessary
  noncomputable theory
  open_locale classical

  --BEGIN--


  /--------------------------------------------------------------------------

  ``cases``
    
    ``cases`` is a general tactic that breaks up complicated terms.
    If ``hpq`` is a term of type ``P ∧ Q`` or ``P ∨ Q`` or ``P ↔ Q``, then use 
    ``cases hpq with hp hq,``.

  ``split``
    
    If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, then use
    ``split,``.

  ``left``/``right``
    
    If the target of the current goal is ``P ∨ Q``, then use 
    either ``left,`` or ``right,`` (choose wisely).

  ``exfalso``

    Changes the target of the current goal to ``false``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  begin
    sorry,
  end

  example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  begin
    sorry,
  end

  example (P Q R : Prop) : P ∧ false ↔ false :=
  begin
    sorry,
  end

  theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q :=
  begin
    sorry,
  end

  --END--

Quantifiers 
============== 
As mentioned it the introduction the *for all* quantifier, ``∀``, is a generalization of a function.
As such the tactics for dealing with ``∀`` are the same as those for ``→``. 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - If ``hp`` is a term of type ``∀ x : X, P x`` and 
      ``y`` is a term of type ``X`` then 
      ``have hpy := hp(y)`` creates a hypothesis ``hpy : P y``.

  * - ``intro``
    - If the target of the current goal is ``∀ x : X, P x``, then 
      ``intro x,`` creates a hypothesis ``x : X`` and 
      changes the target to ``P x``.

The *there exists* quantifier, ``∃``, in type theory is very intuitive. 
If you want to prove a statement ``∃ x : X, P x`` then you need to provide a witness.
If you have a term ``hp : ∃ x : X, P x`` then from this you can extract a witness.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - If ``hp`` is a term of type ``∃ x : X, P x``, then 
      ``cases hp with x key,`` breaks it into 
      ``x : X`` and ``key : P x``.

  * - ``use``
    - If the target of the current goal is ``∃ x : X, P x`` 
      and ``y`` is a term of type ``X``, then 
      ``use y,`` changes the target to ``P y`` and tries to close the goal.

Finally, we know enough Lean tactics to start doing some fun stuff.

Barber paradox
------------------------------------  
Let's disprove the "barber paradox" due to Bertrand Russell. 
The claim is that in a certain town there is a (male) barber that shaves all the men who do not shave themselves. (Why is this a paradox?)
Prove that this is a contradiction.
Here are some :doc:`hints <../hint_1_barber_paradox>` if you get stuck.

.. code-block:: lean

  import tactic
  -- the next two lines let us use the by_cases tactic without trouble
  noncomputable theory
  open_locale classical

  --BEGIN--

  /--------------------------------------------------------------------------

  ``by_cases``

    If ``P`` is a proposition, then ``by_cases P,`` creates two goals,
      the first with a hypothesis ``hp: P`` and
      second with a hypothesis ``hp: ¬ P``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  -- men is type. 
  -- x : men means x is a man in the town
  -- shaves x y is inhabited if x shaves y

  variables (men : Type) (barber : men) 
  variable  (shaves : men → men → Prop)

  example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) := 
    begin 
      sorry,
    end 
  --END--


Mathcampers singing paradox 
------------------------------------
  
Assume that the main lounge is non-empty.
At a fixed moment in time, there is someone in the lounge such that, 
if they are singing, 
then everyone in the lounge is singing. 
(See :doc:`hints <../hint_1_mcsp>`).

.. code:: lean
  :name: lounge_paradox

  import tactic
  -- the next two lines let us use the by_cases tactic without trouble
  noncomputable theory
  open_locale classical

  --BEGIN--

  /--------------------------------------------------------------------------

  ``by_cases``

    If ``P`` is a proposition, then ``by_cases P,`` creates two goals, 
      the first with a hypothesis ``hp: P`` and 
      second with a hypothesis ``hp: ¬ P``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  -- camper is a type. 
  -- If x : camper then x is a camper in the main lounge.
  -- singing(x) is inhabited if x is singing 

  theorem math_campers_singing_paradox  
    (camper : Type) 
    (singing : camper → Prop) 
    (alice : camper) -- making sure that there is at least one camper in the lounge
    : ∃ x : camper, (singing x → (∀ y : camper, singing y)) :=
  begin
    sorry,
  end
  --END--

Relationship conundrum
-----------------------
A relation ``r`` on a type ``X`` is a map ``r : X → X → Prop``.
We say that ``x`` is *related* to ``y`` if ``r x y`` is inhabited.

* ``r`` is reflexive if ``∀ x : X``, ``x`` is related to itself.
* ``r`` is symmetric if ``∀ x y : X``, ``x`` is related to ``y`` implies ``y`` is related to ``x``.
* ``r`` is transitive if ``∀ x y z : X``, ``x`` is related to ``y`` and ``y`` is related to ``x`` implies ``z`` is related to ``z``.
* ``r`` is connected if for all ``x : X`` there is a ``y : Y`` such that ``x`` is related to ``y``.

Show that if a relation is symmetric, transitive, and connected,
then it is also reflexive.

.. code:: lean

  import tactic 
  
  variable X : Type 

  theorem reflexive_of_symmetric_transitive_and_connected
    (r : X → X → Prop)
    (h_symm : ∀ x y : X, r x y → r y x) 
    (h_trans : ∀ x y z : X, r x y → r y z → r x z) 
    (h_connected : ∀ x, ∃ y, r x y) 
  : (∀ x : X, r x x) :=
  begin
    sorry,
  end



Proving "trivial" statements 
=============================
In mathlib, divisibility for natural numbers is defined as the following *proposition*.

.. code:: 

  a ∣ b := (∃ k : ℕ, a = b * k)

For example, ``2 | 4`` will be a proposition ``∃ k : ℕ, 4 = 2 * k``. 
**Very important.** The statement ``2 | 4`` is not saying that "2 divides 4 *is true*". 
It is simply a proposition that requires a proof. 

Similarly, the mathlib library also contains the following definition of ``prime``.

.. code:: 

    def nat.prime (p : ℕ) : Prop 
    := 
      2 ≤ p                                       -- p is at least 2
      ∧                                           -- and 
      ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p            -- if m divides p, then m = 1 or m = p.

Same as with divisibility, for every natural number ``n``, 
``nat.prime n`` is a *proposition*.
So that ``nat.prime 101`` requires a proof.
It is possible to go down the rabbit hole and prove it using just the axioms of natural numbers.
However, this might come at the cost of your sanity.
Fortunately, there are tactics in Lean for proving trivial proofs such as these.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``norm_num``
    - ``norm_num`` is Lean’s calculator. If the target has a proof that involves *only* numbers and arithmetic operations,
      then ``norm_num`` will close this goal.

      If ``hp : P`` is an assumption then ``norm_num at hp,`` tries to use simplify ``hp`` using basic arithmetic operations.

  * - ``ring`` 
    - ``ring,`` is Lean's symbolic manipulator. 
      If the target has a proof that involves *only* algebraic operations, 
      then ``ring,`` will close the goal.

      If ``hp : P`` is an assumption then ``ring at hp,`` tries to use simplify ``hp`` using basic algebraic operations.

  * - ``linarith`` 
    - ``linarith,`` is Lean's inequality solver.
  
  * - ``simp`` 
    - ``simp,`` is a very complex tactic that tries to use theorems from the mathlib library to close the goal. 
      You should only ever use ``simp,`` to *close a goal* because its behavior changes as more theorems get added to the library.

.. code:: lean 

  import tactic data.nat.prime 

  /--------------------------------------------------------------------------

  ``norm_num``

    Useful for arithmetic.
  
  ``ring``

    Useful for basic algebra.

  ``linarith``

    Useful for inequalities.
  
  ``simp``

    Complex simplifier. Use only to close goals.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/
  
  example : 1 > 0 :=
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

  -- you will need the definition 
  -- a ∣ b := (∃ k : ℕ, a = b * k)
  example (m a b : ℕ) :  m + a ∣ m^2 + (a + b) * m + a * b :=
  begin
    sorry,
  end

  -- try ``unfold nat.prime at hp,`` to get started
  example (p : ℕ) (hp : nat.prime p) : ¬ (p = 1) :=
  begin 
    sorry,
  end 

  -- if none of the simplifiers work, try doing ``contrapose!``
  -- sometimes the simplifiers need a little help
  example (n : ℕ) : 0 < n ↔ n ≠ 0 :=
  begin
    sorry,
  end



