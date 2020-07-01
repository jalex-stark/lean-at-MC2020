.. _day1:

************************
Propositions in Lean
************************

Lean is based on logic system called **type theory** instead of **set theory**.
For the most part, you can assume that a **type** is a computer scientist's version of a **set**. Just as a set has elements, a type has **inhabitants**.
The notation

.. code::

  0 : ℕ

stands for "``0`` is an inhabitant of ``ℕ``" i.e. 0 is a natural numbers (yes, in Lean, natural numbers start from ``0``).
You can manipulate types and inhabitants the same way as sets and elements. For example, if ``X`` and ``Y`` are types then

.. code::

  p : X × Y       -- product, p = (x,y) for some x:X, y:Y
  q : X ⊕ Y       -- disjoint union, p = x or p = y for some x:X, y:Y
  f : X → Y       -- function, p(x) = y for x:X and y:Y

Why not just use set theory then? Why bother with type theory?
In type theory you cannot speak of an *element* without a *type*, every element is always an inhabitants of some type.
This makes it easy for computers to verify the correctness of statements.
As far as proving theorems is concerned, the most drastic difference comes from the paradigm of **propositions as types**.


Propositions as types
======================

In set theory, a **proposition** is a statement that has the potential of being true or false, like ``2 + 2 = 4``, ``2 + 2 = 5``, "Fermat's last theorem", or "Riemann hypothesis".
In type theory, there is a special type called ``Prop`` whose inhabitants are propositions (along with appropriate axioms).
Further, each proposition ``P`` is itself a type and the inhabitants of ``P`` are its proofs!

.. code::

    P : Prop     -- P is a proposition
    hp : P       -- hp is a proof of P

As such, in type theory "producing a proof of ``P``" is the same as "producing an inhabitant of ``P``".
This is the biggest change in perspective you need to be able to work with type theory.

**Notation.** Throughout these notes, we'll let ``P, Q, R, ...`` denote propositions unless otherwise specified.

Implication 
------------
In set theory, the proposition ``P ⇒ Q`` ("P implies Q") is true if either both ``P`` and ``Q`` are true or if ``P`` is false. 
In type theory, a proof of an implication ``P ⇒ Q`` is just a function ``f : P → Q``.
Given a function ``f : P → Q``, every proof ``hp : P`` produces a proof ``f(hp) : Q``.
If ``P`` is false then ``P`` is *empty*, and there exists an `empty function <https://en.wikipedia.org/wiki/Function_(mathematics)#empty_function>`_ from an empty type to any type.
Hence, we will use ``→`` to indicate implication.


Negation 
----------
In set theory, the negation of a proposition ``¬ P`` is true/false if and only if ``P`` is false/true.
In type theory, there is a special proposition ``false : Prop`` which has no proof (i.e. no inhabitant and hence is *empty*).
The negative of a proposition ``¬ P`` is then just a function ``f : P → false``.
Such a function exists if and only if ``P`` itself is empty (`empty function <https://en.wikipedia.org/wiki/Function_(mathematics)#empty_function>`_ ), hence ``P → false`` is inhabited if and only if ``P`` is empty which justifies using it as the definition of ``P → false``.


.. topic:: Propositions as Types

  1. Proving a proposition ``P : Prop`` is equivalent to producing an inhabitant ``hp : P``.
  2. Proving an implication ``P → Q`` is equivalent to producing a function ``f : P → Q``.
  3. The negation ``¬ P`` is defined as the implication ``P → false``.




Logic in Lean 
==============================

In Lean, a theorem and its proof is written using the following syntax.

.. code:: lean

  theorem fermats_last_theorem 
    (n : ℕ) 
    (n_gt_2 : n > 2) 
    : 
    ¬ (∃ x y z : ℕ, (x^n + y^n = z^n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0))
  := 
  begin 
    sorry,
  end


Let us parse the above statement. Lean ignores whitespace so spaces and new-lines don't affect the code. 
We could have written the entire code in a single line. But that way madness lies.

* ``theorem`` is a special keyword. It means that whatever is to follow is a proposition. 
  You'll sometimes see ``lemma`` instead of ``theorem`` which means the exact same thing.
* ``fermats_last_theorem`` is the name of the theorem. 
* ``(n : ℕ)`` and ``(n_gt_2 : n > 2)`` are the two **hypotheses**. 
  The former says ``n`` is a natural number and the latter says that ``n_gt_2`` is a proof of ``n>2`` (and hence ``n>2`` is true).
* ``:`` is the delimiter between hypotheses and targets
* ``¬ (∃ x y z : ℕ, (x^n + y^n = z^n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0)`` is the **target** of the theorem.
* ``:=`` denotes the start of proof. 
* ``begin`` and ``end`` denote the start and end of **tactics mode**. When you enter tactics mode, Lean opens up a goal for you with the given assumptions and target. 
  If you place your cursor before ``sorry`` or after ``begin`` you'll see the following in the goal window.

  .. code:: 

    n : ℕ,
    n_gt_2 : n > 2
    ⊢ ¬∃ (x y z : ℕ), x ^ n + y ^ n = z ^ n ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0

  A proof always starts with one goal with (possibly) multiple hypothesis and one target. 
  But as you move along you can create multiple goals each with their own target.
* ``sorry,`` is an example of a tactic. 
  Tactics are a type of command used for theorem proving in Lean.
  The tactic ``sorry,`` is a way of telling Lean "I give up ;_;	". 
  If you use ``sorry,`` in your proof Lean will have pity on you and let you move on and will produce a warning that sorry is being used.

   
.. topic:: Very Important

  Very important: Note that tactics must end with a comma (,) 



Implications in Lean 
---------------------
We'll start learning tactics by proving implications in Lean.
The first two tactics we'll learn is ``exact,`` and ``intros _,``. 

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``exact``
     - If ``hp : P`` is a hypothesis and 
       ``⊢ P`` is the target then ``exact hp,`` will close the goal.
       You can use complicated functions in place of ``hp``. 
       For example, if ``hp : P`` and ``f : P → Q`` are hypothesis and the target is ``⊢ Q``
       then ``exact f(hp),`` will close the goal.

       Mathematically, this saying "this is *exactly* what we were required to proved".

   * - ``intro``
     - If the target of the current goal is a function ``⊢ P → Q``, 
       then ``intro hp,`` will produce a hypothesis 
       ``hp : P`` and change the target to  ``⊢ Q``.

.. code:: lean
  :name: exact_intros_examples

  -- if P is true, then P is true.
  theorem tautology (P : Prop) (hp : P) : P :=
  begin
    sorry,
  end

  -- if P is true, then P is true.
  theorem tautology' (P : Prop) : P → P :=
  begin
    sorry,
  end

  -- If P is true, then every proposition implies P.
  example (P Q : Prop): (P → (Q → P)) := 
  begin 
    sorry,
  end 

  -- Can you find two different ways of proving the following?
  example (P Q : Prop) : ((Q → P) → (Q → P)) := 
  begin 
    sorry,
  end 

The next two tactics are ``have`` and ``apply``.

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``have``
     - One use of the tactic ``have`` is to create intermediate variables. 
       If ``f : P → Q`` is a hypothesis, then
       ``have hp := f (p),`` adds the hypothesis ``hp : Q`` .
     
   * - ``apply``
     - The tactic ``apply`` is used for reasoning backward. 
       If the target of the current goal is a function ``⊢ Q`` and 
       ``f : P → Q`` is a hypothesis, then  
       ``apply f,`` changes target to ``⊢ P``.

       Mathematically, this is equivalent to saying "because P implies Q, to prove Q it suffices to prove P".

.. code:: lean 
  :name: have_apply_examples 

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S : Prop) (f : P → Q) (g : Q → R) : P → R :=
  begin
    sorry,
  end

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S : Prop) 
    (hp : P) 
    (f : P → Q) 
    (g : Q → R) 
    : R :=
  begin
    sorry,
  end

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S T U: Type)
  (hpq : P → Q)
  (hqr : Q → R)
  (hqt : Q → T)
  (hst : S → T)
  (htu : T → U)
  : P → U :=
  begin
    sorry,
  end

For the following exercises, remember that ``¬ P`` is defined as the implication ``P → false``,
``¬ ¬ P`` is ``(P → false) → false``, and so on.

.. code:: lean

  theorem self_imp_not_not_self (P : Prop) : P → ¬ ¬ P :=
  begin
    sorry,
  end

  theorem soundness (P : Prop) : P → (¬ P → false) :=
  begin
    sorry,
  end

  theorem contrapositive (P Q : Prop) : (¬Q → ¬P) → (P → Q)
  begin
    sorry,
  end

  -- need to provide a hint for this problem 
  example (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
  begin
    sorry,
  end



Proof by contradiction
------------------------
As it turns out, the converses of three above theorems cannot be proven using just ``exact``, ``intro``, ``have``, and ``apply``.
See for yourself.

.. code:: lean

  theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
  begin
    sorry,
  end

  theorem soundness (P : Prop) : P → (¬ P → false) :=
  begin
    sorry,
  end

  theorem contrapositive_converse (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  begin
    sorry,
  end

  -- need to provide a hint for this problem 
  example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
  begin
    sorry,
  end

This is another point where type theory diverges from set theory.
In type theory, it is not true that ``¬ ¬ P = P``, *by definition*. 
There is an extra axiom called **the law of excluded middle** which says that 
either ``P`` is inhabited or ``¬ P`` is inhabited (and there is no third *middle* option). 
This is the axiom that allows for proofs by contradiction. 
Lean provides us the following tactics to use it.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``exfalso``
    - Changes the target of the current goal to ``⊢ false``.
      
      The name derives from "ex falso, quodlibet" which translates to "from contradiction, anything". 
      You should use this tactic when there are contradictory hypotheses present. 
  
  * - ``by_cases``
    - If ``P : Prop``, then ``by_cases P,`` creates two goals, 
      the first with a hypothesis ``hp: P`` and second with a hypothesis ``hp: ¬ P``.

      Mathematically, this is saying either ``P`` is true or ``P`` is false.
      ``by_cases`` is the most direct application of the law of excluded middle.

  * - ``by_contradiction``
    - If the target of the current goal is  ``⊢ Q``,
      then ``by_contradiction,`` changes the target to  ``⊢ false`` and 
      adds ``hnq : ¬ P`` as an assumption. 

      Mathematically, this is proof by contradiction. 
  
  * - ``push_neg``
    - The tactic ``push_neg,`` simplifies negations in the target. 
      For example, if the target of the current goal is ``⊢ ¬ ¬ ¬ P`` then 
      ``push_neg,`` simplifies it to ``⊢ ¬ ¬ P``. 
      
      ``push_neg,`` also simplifies across quantifiers. 
      For example, if the target is ``⊢ : ¬ ∀ x, ∃ y, x ≤ y`` will be transformed by ``push_neg,`` into ``⊢: ∃ x, ∀ y, y < x``. 

      Finally, you can push negations across a hypothesis ``hp : P`` using ``push_neg at hp,``.

  * - ``contrapose!``
    - If the target of the current goal is  ``⊢ P → Q``,
      then ``contrapose!,`` changes the target to  ``⊢ ¬ Q → ¬ P``.

      If the target of the current goal is ``⊢ Q`` 
      and one of the hypotheses is ``hp : P``,
      then ``contrapose! hp,`` changes the target to  ``⊢ ¬ P`` 
      and changes the hypothesis to ``hp : ¬ Q``.

      Mathematically, this is proving the contrapositive of the goal (which is equivalent to it).


.. code:: lean

  import tactic

  -- these two statements tell Lean to use the law of excluded middle as necessary
  noncomputable theory
  open_locale classical
  

  --BEGIN--

  theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
  begin
    sorry,
  end

  theorem contrapositive_converse (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  begin
    sorry,
  end

  -- need to provide a hint for this problem 
  example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
  begin
    sorry,
  end

  --END--


Logical operators
----------------------------------------
In Lean, we use 
``∧`` to denote **and**, 
``∨`` to denote **or**, 
and ``↔`` to denote **iff**. 

In type theory, a proposition ``(∀ x : X, P x)`` is just a function ``X → Prop`` which sends ``x : X`` to ``P x``.
The tactics for dealing with ``∀`` are hence exactly ones as for ``→``.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - ``cases`` is a general tactic that breaks a complicated hypothesis into simpler ones.

      If  ``hpq : P ∧ Q`` is a hypothesis, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``.

      If  ``hpq : P × Q`` is a hypothesis, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``. 

      If  ``fg : P ↔ Q`` is a hypothesis, then 
      ``cases fg with f g,`` breaks it into ``f : P → Q`` and ``g : Q → P``.

      If  ``hpq : P ∨ Q`` is a hypothesis, then 
      ``cases hpq with hp hq,`` creates two goals and adds the hypotheses ``hp : P`` and ``hp : Q`` to one each.

      If ``hp : (∃ x : X, P x)`` is a hypothesis, then 
      ``cases hp with x key,`` breaks it into ``x : X`` and ``key : P x``.

  * - ``split``
    - If the target of the current goal is ``⊢ P ∧ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``⊢ P`` and ``⊢ Q``.

      - If the target of the current goal is ``⊢ P × Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``⊢ P`` and ``⊢ Q``.

      If the target of the current goal is ``⊢ P ↔ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``⊢ P → Q`` and ``⊢ Q → P``.

  * - ``left``
    - If the target of the current goal is ``⊢ P ∨ Q``, then 
      ``left,`` changes the target to ``⊢ P``.
  
  * - ``right``
    - If the target of the current goal is ``⊢ P ∨ Q``, then 
      ``right,`` changes the target to ``⊢ Q``.

  * - ``use``
    - If the target of the current goal is ``⊢ ∃ x : X, P x`` 
      and ``y : X,`` is a hypothesis, then 
      ``use y,`` changes the target to ``⊢ P y``.


.. code:: lean
  :name: and_or_example

  example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  begin
    sorry,
  end

  example (P Q : Prop) : P ∧ Q → P ∨ Q :=
  begin
    sorry,
  end

  example (P Q R : Prop) : (P → R) ∧ (Q → R) → ((P ∨ Q) → R):=
  begin
    sorry,
  end

.. todo:: 

  Copy problems from theorem proving in lean here. 


.. todo:: 

  Composition of surjective functions is surjective.

.. todo:: 

  Russell's paradox,


Lounge paradox
--------------------------------------------
There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. code:: lean
   :name: lounge_paradox

    import tactic
    -- the next two lines let us use the by_cases tactic without trouble
    noncomputable theory
    open_locale classical

    theorem lounge {camper : Type u} (playing : camper → Prop) [inhabited camper] :
      ∃ x, (playing x → ∀ y, playing y) :=
    begin
      have alice := arbitrary camper, -- this works because of "inhabited" above
      by_cases h : ∃ bob, ¬ playing bob,
    end