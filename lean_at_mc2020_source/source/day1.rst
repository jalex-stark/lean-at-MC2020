.. _day1:

********
Basics
********

.. todo::

  add currying and uncurrying problem somewhere.

Lean is based on logic system called **type theory** instead of **set theory**.
For the most part, you can assume that a **type** is a computer scientists version of a **set**. Just as a set has elements, a type has **inhabitants**.
The notation

.. code::

  0 : ℕ

stands for "``0`` is an inhabitant of ``ℕ``" i.e. 0 is a natural numbers (yes, in Lean, natural numbers start from ``0``).
You can manipulate types and inhabitants the same way as sets and elements. For example, if ``X`` and ``Y`` are types then

.. code::

  p : X × Y       -- product, p = (x,y)        for some x:X, y:Y
  q : X ⊕ Y       -- disjoint, p = x or p = y  for some x:X, y:Y
  f : X → Y       -- functions, p(x) = y       for x:X and y:Y

Why not just use set theory then? Why bother with type theory?
In type theory you cannot speak of an *element* without a *type*, all elements are always inhabitants of certain types.
This makes it easy for computers to check statements.
From the mathematics perspective, the most drastic difference comes from the paradigm of **propositions as types**.


A **proposition** is a statement that has a potential of being true or false, like ``2 + 2 = 4``, ``2 + 2 = 5``, "Fermat's last theorem", or "Riemann hypothesis".
Just like we can have concrete sets in Lean like ``ℕ``, and abstract sets called things like ``X``, we can also have concrete propositions like ``2 + 2 = 5`` and abstract propositions called things like ``P``. In type theory, there is a type ``Prop`` whose inhabitants are propositions.
Further, each proposition ``P`` is itself a type and the inhabitants of ``P`` are its proofs!

.. code::

    P : Prop     -- P is a proposition
    hp : P       -- hp is a proof of P

And so in type theory "producing a proof of ``P``" is the same as "producing an inhabitant of ``P``".
This is the biggest change in perspective you need to be able to work with type theory.

.. topic:: Very Important

  Proving a proposition ``P: Prop`` is equivalent to producing an inhabitant ``hp : P``.


**Notation:** In this section, ``P, Q, ...`` will denote propositions and ``hp, hq, ...`` will denote their proofs.



The simplest **tactic** in Lean is the ``exact`` tactic. This is the tactic equivalent of the mathematical statement "This is *exactly* what the theorem is asking us to prove, hence we are done". Let's prove a simple statement.

.. code:: lean
  :name: tautology

  -- P is a proposition
  variables P : Prop

  -- if P is true then P is true.
  theorem tautology (hp : P) : P :=
  begin
    sorry,
  end

Given a proof ``hp:P`` we want to produce a proof of ``P``. But that's just ``hp``!
We tell Lean to use ``hp`` to "close the goal" by saying

.. code::

  exact hp,

Try replacing ``sorry`` with ``exact hp,`` in the above proof.




Propositional Logic
====================

Propositional logic provides the logical operators **implies** (``→``), **or** (``∨``), **and** (``∧``), **negation** (``¬``) for combining simple propositions to create complex ones.

**or** (``∨``), **and** (``∧``), in type theory are exactly the same as in set theory.

There are two tactics in Lean for dealing with ``∧``:

1. ``split``
2. ``cases``

and three tactics in Lean for dealing with ``∨``:

1. ``left``
2. ``right``
3. ``cases``

Their use is best explained through examples.


.. code:: lean
  :name: and_or_example

  /---------------------------------------------------------------

  Tactics used for the ∧ (and) operator: split and cases
  Tactics used for the ∨ (or) operator: left/right and cases

  --------------------------------------------------------------/

  -- If P ∧ Q is true then P is true.
  example (P Q : Prop) (hpq : P ∧ Q) : P :=
  begin
    cases hpq with hp hq,
    exact hp,
  end

  -- If P is true and Q is true then P ∧ Q is true.
  example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  begin
    split,
    exact hp,
    exact hq,
  end

  -- If P is true then P ∨ Q is true.
  example (P Q : Prop) (hp : P) : P ∨ Q :=
  begin
    left,
    exact hp,
  end

  -- If P ∨ P is true then P is true.
  example (P : Prop) (hpp : P ∨ P) : P :=
  begin
    cases hpp with hp1 hp2,
    exact hp1,
    exact hp2,
  end

  /---------------------------------------------------------------

  Your turn.

  --------------------------------------------------------------/

  -- If P ∧ Q is true then Q ∧ P is true.
  example (P Q : Prop) (hpq : P ∧ Q) : Q ∧ P :=
  begin
    sorry,
  end

  -- If P ∧ Q is true then Q ∧ P is true.
  example (P Q : Prop) (hpq : P ∧ Q) : Q ∧ P :=
  begin
    sorry,
  end

  -- If P ∨ Q is true then Q ∨ P  is true.
  example (P Q : Prop) (hpq : P ∨ Q) : Q ∨ P :=
  begin
    sorry,
  end

  -- If P ∧ Q is true then P ∨ Q is true.
  example (P Q : Prop) (hpq : P ∧ Q) : P ∨ Q :=
  begin
    sorry,
  end


**implies** (``→``) is a very interesting operator in type theory.
A proof of ``P → Q`` is very literally a function ``f : P → Q``.

In set theory, ``P → Q`` is true if either both ``P`` and ``Q`` are true (case 1) or if ``P`` is false (case 2).
If there is a function ``f : P → Q`` then every proof ``hp : P`` produces a proof ``f(hp) : Q`` (case 1).
If ``P`` is false then ``P`` is *empty*, and there is always an `empty function`_ from an empty type to any type ``Q`` (case 2).
There are four different tactics you can use to deal with **implies** (``→``)

1. ``intros``
2. ``apply``
3. ``have``
4. ``exact``


.. _`empty function`: https://en.wikipedia.org/wiki/Function_(mathematics)#empty_function

.. code:: lean
  :name: implies_examples

  /-------------------------------------------------------------------------

  Tactics used for the → (implies) operator: intros, apply, have, exact

  --------------------------------------------------------------------------/

  -- P implies P.
  theorem tautology2 (P: Prop) : P → P :=
  begin
    intros hp,
    exact hp,
  end

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S : Prop) (f : P → Q) (g : Q → R) : P → R :=
  begin
    intros hp,
    have hq := f (hp),
    exact g (hq),
  end

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S : Prop) (hp : P) (f : P → Q) (g : Q → R) : R :=
  begin
    apply g,
    apply f,
    exact hp,
  end

  -- If P implies Q and Q implies R then P implies R.
  example (P Q R S : Prop) (hp : P) (f : P → Q) (g : Q → R) : R :=
  begin
    have hq := f (hp),
    apply g,
    exact hq,
  end


  /-------------------------------------------------------------------------

  Your turn.

  --------------------------------------------------------------------------/

  example (P Q : Prop) : P → (Q → P) :=
  begin
    sorry,
  end

  example (P Q R : Prop) : (P → R) ∧ (Q → R) → ((P ∨ Q) → R):=
  begin
    sorry,
  end

  -- need some more problems here



**negation** (``¬``) is another very interesting operator in type theory.
There is a proposition ``false : Prop`` in type theory which has no proof (and is *empty*).
The negative of a proposition ``¬ P`` is a function ``f : P → false``.
This follows from the fact that if a proposition implies a false proposition then it must itself be false.
The tactics negation are the same as the tactics for ``implies``.


.. code:: lean

  /-------------------------------------------------------------------------

  Tactics used for the ¬ (negation) operator: intros, apply, have, exact

  --------------------------------------------------------------------------/

  theorem contrapositive (P Q : Prop) : (Q → P) → (¬P → ¬Q) :=
  begin
    -- remember that if the target is ⊢ ¬Q then intros hq, will create a hypothesis hq : Q
    sorry,
  end

  theorem (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
  begin
    sorry,
  end




.. table::
  :widths: 15, 45, 45

  +--------------+------------------------------------------+--------------------------------------------+
  |              | Target                                   | Hypothesis                                 |
  +==============+==========================================+============================================+
  |              |                                          |                                            |
  | **implies**  | ``intros``                               | ``apply``                                  |
  |              |                                          |                                            |
  | ``→``        | If                                       | If                                         |
  |              | ``⊢ P → Q``                              | ``⊢ Q``                                    |
  |              | is the target of the current goal,       | is the target of the current goal,         |
  |              | then                                     | and                                        |
  |              | ``intros hp,``                           | ``f : P → Q``                              |
  |              | adds                                     | is a hypothesis, then                      |
  |              | ``hp : P``                               | ``apply f,``                               |
  |              | as a hypothesis and change the target to | changes the target to ``P``.               |
  |              | ``⊢ Q``.                                 +--------------------------------------------+
  |              |                                          |                                            |
  |              |                                          | ``have``                                   |
  |              |                                          |                                            |
  |              |                                          | If                                         |
  |              |                                          | ``f : P → Q`` and ``hp: P``                |
  |              |                                          | are hypotheses in the current goal, then   |
  |              |                                          | ``have hq := f(hp),``                      |
  |              |                                          | creates a new hypothesis                   |
  |              |                                          | ``hq : Q``.                                |
  |              |                                          +--------------------------------------------+
  |              |                                          | ``exact``                                  |
  |              |                                          |                                            |
  |              |                                          | If                                         |
  |              |                                          | ``f : P → Q``                              |
  |              |                                          | and                                        |
  |              |                                          | ``hp: P``                                  |
  |              |                                          | are hypotheses in the current goal,        |
  |              |                                          | and the target is                          |
  |              |                                          | ``⊢ Q``                                    |
  |              |                                          | then                                       |
  |              |                                          | ``exact f(hp),``                           |
  |              |                                          | closes the goal.                           |
  +--------------+------------------------------------------+--------------------------------------------+
  | **negation** | ``intros``                               | ``apply``                                  |
  |              |                                          |                                            |
  | ``¬``        | If                                       | If                                         |
  |              | ``⊢ ¬ P``                                | ``⊢ false``                                |
  |              | is the target of the current goal,       | is the target of the current goal,         |
  |              | then                                     | and                                        |
  |              | ``intros hp,``                           | ``hnp : ¬ P``                              |
  |              | adds                                     | is a hypothesis,                           |
  |              | ``hp : P``                               | then                                       |
  |              | as a hypothesis and change the target to | ``apply hnp,``                             |
  |              | ``⊢ false``.                             | changes the target to                      |
  |              |                                          | ``P``.                                     |
  |              |                                          +--------------------------------------------+
  |              |                                          | ``exact``                                  |
  |              |                                          |                                            |
  |              |                                          | If                                         |
  |              |                                          | ``hnp : ¬ P``                              |
  |              |                                          | and                                        |
  |              |                                          | ``hp: P``                                  |
  |              |                                          | are hypotheses in the current goal,        |
  |              |                                          | and                                        |
  |              |                                          | ``⊢ false``                                |
  |              |                                          | is the target, then                        |
  |              |                                          | ``exact hnp(hp),``                         |
  |              |                                          | closes the goal.                           |
  +--------------+------------------------------------------+--------------------------------------------+
  |              |                                          |                                            |
  | **or**       | ``left`` / ``right``                     | ``cases``                                  |
  |              |                                          |                                            |
  | ``∨``        | If                                       | If                                         |
  |              | ``⊢ P ∨ Q``                              | ``hpq : P ∨ Q``                            |
  |              | is the target of the current goal,       | is a hypothesis in the current goal,       |
  |              | then                                     | then                                       |
  |              | ``left,``                                | ``cases hpq with hp hq,``                  |
  |              | changes the target to                    | produces two new goals with the hypotheses |
  |              | ``⊢ P``                                  | ``hp : P``                                 |
  |              | and                                      | and                                        |
  |              | ``right,``                               | ``hq : Q``                                 |
  |              | changes the target to                    | respectively.                              |
  |              | ``⊢ Q``.                                 |                                            |
  +--------------+------------------------------------------+--------------------------------------------+
  |              |                                          |                                            |
  | **and**      | ``split``                                | ``cases``                                  |
  |              |                                          |                                            |
  | ``∧``        | If                                       | If                                         |
  |              | ``⊢ P ∧ Q``                              | ``hpq : P ∧ Q``                            |
  |              | is the target of the current goal,       | is a hypothesis for the current goal,      |
  |              | then                                     | then                                       |
  |              | ``split,``                               | ``cases hpq with hp hq,``                  |
  |              | produces two goals with targets          | produces two new hypotheses                |
  |              | ``⊢ P``                                  | ``hp : P``                                 |
  |              | and                                      | and                                        |
  |              | ``⊢ Q``                                  | ``hq : Q``.                                |
  |              | with the same set of assumptions.        |                                            |
  +--------------+------------------------------------------+--------------------------------------------+
  |              |                                          |                                            |
  | **iff**      | ``split``                                | ``cases``                                  |
  |              |                                          |                                            |
  | ``↔``        | If                                       | If                                         |
  |              | ``⊢ P ↔ Q``                              | ``hfg : P ↔ Q``                            |
  |              | is the target of the current goal,       | is a hypothesis for the current goal, then |
  |              | then                                     | ``cases hpq with hf hg,``                  |
  |              | ``split,``                               | produces two new hypotheses                |
  |              | produces two goals with targets          | ``hf : P → Q``                             |
  |              | ``⊢ P → Q``                              | and                                        |
  |              | and                                      | ``hg : Q → P``.                            |
  |              | ``⊢ Q → P``                              |                                            |
  |              | with the same set of hypotheses.         |                                            |
  +--------------+------------------------------------------+--------------------------------------------+





Law of excluded middle
===========================================

We often do *proofs by contradiction* in math. 
This requires an axiom called the *law of excluded middle* which says that every proposition ``P`` is either *true* or *false*.
The following tactics in Lean let you invoke the law of excluded middle. 

.. table::
  :widths: 30, 70

  +-----------------------------+-------------------------------------------------------------------+
  | ``exfalso,``                | Changes the target of the current goal to                         |
  |                             | ``⊢ false``.                                                      |
  +-----------------------------+-------------------------------------------------------------------+
  | ``by_cases P with hp hnp,`` | First creates a hypothesis                                        |
  |                             | ``hpnp : P ∨ ¬ P``                                                |
  |                             | and then applies                                                  |
  |                             | ``cases hpnp with hp hnp``.                                       |
  +-----------------------------+-------------------------------------------------------------------+
  | ``contrapose!,``            | If the target of the current goal is                              |
  |                             | ``⊢ P → Q``                                                       |
  |                             | then                                                              |
  |                             | ``contrapose!,``                                                  |
  |                             | changes the goal to                                               |
  |                             | ``⊢ ¬ Q → ¬ P``                                                   |
  |                             | and simplify the negations.                                       |
  +-----------------------------+-------------------------------------------------------------------+
  | ``contrapose! hp,``         | If the target of the current goal is                              |
  |                             | ``⊢ Q``                                                           |
  |                             | and one of the hypotheses is                                      |
  |                             | ``hp : P``                                                        |
  |                             | then                                                              |
  |                             | ``contrapose! hp,``                                               |
  |                             | changes the target to                                             |
  |                             | ``⊢ ¬ P``,                                                        |
  |                             | change the hypothesis to                                          |
  |                             | ``hp : ¬ Q``,                                                     |
  |                             | and simplify the negations.                                       |
  +-----------------------------+-------------------------------------------------------------------+
  | ``by_contradiction,``       | If the target of the current goal is                              |
  |                             | ``⊢ Q``                                                           |
  |                             | then                                                              |
  |                             | ``by_contradiction,``                                             |
  |                             | changes the target to                                             |
  |                             | ``⊢ false``                                                       |
  |                             | and add a hypothesis                                              |
  |                             | ``hnq : ¬ Q``.                                                    |
  +-----------------------------+-------------------------------------------------------------------+
  | ``push_neg,``               | Tries to simplify the negations in the target of the current goal |
  +-----------------------------+-------------------------------------------------------------------+
  | ``push_neg at hp,``         | Tries to simplify the negations in the hypothesis ``hp: P``       |
  +-----------------------------+-------------------------------------------------------------------+

.. code:: lean

  import tactic
  -- 
  noncomputable theory
  open_locale classical

  --BEGIN--

  /-------------------------------------------------------------------------

  Proofs that require law of excluded middle.

  --------------------------------------------------------------------------/

  example (P Q : Prop) : (¬P ∨ P) → Q :=
  begin
    sorry,
  end

  example (P Q : Prop) : (P → Q) → (¬P ∨ Q) :=
  begin
    sorry,
  end

  example (P : Prop) : P ∨ ¬P :=
  begin
    sorry,
  end

  example (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q :=
  begin
    sorry,
  end

  example (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
  begin
    sorry,
  end

  --END--
  
  


First order logic
=================

.. table::
  :widths: 15, 45, 45

  +------------+---------------------------------------+--------------------------------------------------+
  |            | Goal                                  | Assumption                                       |
  +------------+---------------------------------------+--------------------------------------------------+
  |            |                                       |                                                  |
  | **forall** | ``intro``                             | ``have``                                         |
  |            |                                       |                                                  |
  | ``∀``      | If the target of the current goal is  | If in the current goal there are hypotheses      |
  |            | ``⊢ ∀ x : X, P x``,                   | ``hP : ∀ x: X, P x``                             |
  |            | then                                  | and                                              |
  |            | ``intro x,``                          | ``y : X``,                                       |
  |            | creates a hypothesis                  | then                                             |
  |            | ``x : X``                             | ``have hpy :=  hP y,``                           |
  |            | and changes the target to             | creates a new hypothesis                         |
  |            | ``⊢ P x``.                            | ``hpy : P y``.                                   |
  +------------+---------------------------------------+--------------------------------------------------+
  |            |                                       |                                                  |
  | **exists** | ``use``                               | ``cases``                                        |
  |            |                                       |                                                  |
  | ``∃``      | If the target of the current goal is  | If one of the hypotheses in the current goal is  |
  |            | ``⊢ ∃ x : X, P x``                    | ``hp : ∃ x: X, P x``,                            |
  |            | and one of the hypotheses is          | then                                             |
  |            | ``y : X``,                            | ``cases hp with x hpx``                          |
  |            | then                                  | produces two new hypotheses                      |
  |            | ``use y,``                            | ``x : X``                                        |
  |            | changes the target to                 | and                                              |
  |            | ``P y``.                              | ``hpx : P x``.                                   |
  +------------+---------------------------------------+--------------------------------------------------+

Need some simple examples here.

.. code:: lean
   :name: lounge_paradox

    import tactic
    -- the next two lines let us use the by_cases tactic without trouble
    noncomputable theory
    open_locale classical

    --BEGIN--
    
    theorem lounge {camper : Type u} (playing : camper → Prop) [inhabited camper] :
      ∃ x, (playing x → ∀ y, playing y) :=
    begin
      have alice := arbitrary camper, -- this works because of "inhabited" above
      by_cases h : ∃ bob, ¬ playing bob,
    end

    --END--



.. Problems
.. ===========

.. Triple negation without LEM
.. ---------------------------
.. This exercise follows directly from classical.not_not.
.. However, classical.not_not introduces axioms that we don't need for this question.
.. Can you do this in tactic mode with only intro, apply, and exact?

.. .. code:: lean
..    :name: triple_negation

..     theorem (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
..     begin
..       intro nnnp,
..     end



.. Lounge paradox
.. --------------------------------------------
.. There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. .. code:: lean
..    :name: lounge_paradox

..     import tactic
..     -- the next two lines let us use the by_cases tactic without trouble
..     noncomputable theory
..     open_locale classical

..     theorem lounge {camper : Type u} (playing : camper → Prop) [inhabited camper] :
..       ∃ x, (playing x → ∀ y, playing y) :=
..     begin
..       have alice := arbitrary camper, -- this works because of "inhabited" above
..       by_cases h : ∃ bob, ¬ playing bob,
..     end

.. Odds and evens
.. ---------------
.. Here's an example with statements about natural numbers.
.. We started the proof by rewriting with something from the library.
.. Try finishing the proof with just your logic tools --- you shouldn't need to know how natural numbers are implemented.

.. .. code:: lean
..    :name: odds_and_evens

..     import tactic
..     import data.nat.parity

..     lemma even_of_odd_add_odd
..       {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
..     nat.even (a + b) :=
..     begin
..       rw nat.even_add,
..     end
