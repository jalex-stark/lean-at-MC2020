.. _day1:

********
Basics 
********

Lean is based on **type theory** instead of **set theory**. 
For the most part, you can assume that a **type** is a computer scientists version of a set. Just as a set has elements, a type has **inhabitants**. The notation 

.. code::   

  0 : ℕ

stands for ``0`` is an inhabitant of ``ℕ`` i.e. 0 is a natural numbers (yes, in Lean natural numbers start from ``0``).
You can manipulate types and inhabitants the same way as sets and elements. For example, if ``X`` and ``Y`` are types then

.. code::   

  p : X × Y       -- product, p = (x,y)        for some x:X, y:Y
  q : X ⊕ Y       -- disjoint, p = x or p = y  for some x:X, y:Y 
  f : X → Y       -- functions, p(x) = y       for x:X and y:Y



Propositional Logic 
====================
A **proposition** is a statement that has a potential of being true or false, like ``2 + 2 = 4``, ``2 + 2 = 5``, "Fermat's last theorem", or "Riemann hypothesis".
Just like we can have concrete sets in Lean like ``ℕ``, and abstract sets called things like ``X``, we can also have concrete propositions like ``2 + 2 = 5`` and abstract propositions called things like ``P``. 

.. code:: 
    
    P : Prop     -- P is a proposition 
    hp : P       -- hp is a proof of P

In type theory, there is a type ``Prop`` whose inhabitants are propositions.
Further, each proposition ``P`` is itself a **type** and the inhabitants of ``P`` are its proofs!


.. topic:: Very Important

  Proving a proposition ``P: Prop`` is equivalent to producing an inhabitant ``hp : P``.


**Notation:** In this section, ``P, Q, ...`` will denote propositions and ``hp, hq, ...`` will denote their proofs.





Implies
-----------------------
Let's prove a simple statement.

.. code:: lean 
  :name: tautology

  -- P is a proposition 
  variables P:Prop

  --BEGIN--
  -- if P is true then P is true.
  theorem tautology (hp:P) : P :=      
  begin 
    sorry, 
  end 
  --END--

Here, we are saying given a proof ``hp:P`` produce a proof of ``P``. But that's just ``hp``! 
We tell Lean to use ``hp`` to "close the goal" by saying 

.. code:: 

  exact hp, 

Try replacing ``sorry`` with ``exact hp,`` in the above proof. 


Here's another way to describe the exact same statement. 

.. code:: lean 
  :name: tautology2

  -- P is a proposition 
  variables P:Prop

  --BEGIN--
  -- P implies P
  theorem tautology2 : P → P :=      
  begin 
    sorry, 
  end 
  --END-- 

Here, our goal is to produce a function ``f: P → P``. [#to]_ To do this, given an arbitrary proof ``hp:P`` we want to produce a proof of ``P``. To do this we use the ``intro`` tactic. Replace the ``sorry`` in the above proof with the following command.

.. code:: 

  intro hp,


How does this change the goal? Can you finish the proof now?

.. [#to] You can produce the ``→`` sign by typing ``\to`` followed by a space.






And 
----

.. code:: lean 

  -- P is a proposition 
  variables P Q:Prop

  --BEGIN--
  -- (P and Q) implies (Q and P).
  example : P ∧ Q → Q ∧ P :=      
  begin 
    sorry, 
  end 
  --END--

You can start the proof by ``intro hpq`` which will produce 

.. code:: 

  hpq: P ∧ Q
  ⊢ Q ∧ P

Now we will need two tactics: ``cases`` and ``split``

1. Writing ``cases hpq with hp hq`` breaks up ``hpq: P ∧ Q`` into two ``hp:P`` and ``hq:Q``.
2. Writing ``split,`` breaks up the goal ``⊢ Q ∧ P`` into two different goals ``⊢ Q`` and ``⊢ Q`` and Lean will then focus on one goal at a time.

Your turn.




Or 
----

.. code:: lean 

  -- P is a proposition 
  variables P Q:Prop

  --BEGIN--
  -- (P or Q) implies (Q or P).
  example : P ∨ Q → Q ∨ P :=      
  begin 
    sorry, 
  end 
  --END--

You can start the proof by ``intro hpq`` which will produce 

.. code:: 

  hpq: P ∨ Q
  ⊢ Q ∨ P


Now we will need three tactics: ``cases``, ``left``, ``right``

1. Writing ``cases hpq with hp hq`` produces two goals: 
    * one with the assumption ``hp: P`` 
    * another with the assumption ``hq:Q``.
2. Writing ``left`` produces the new goal ``⊢ Q``.
3. Writing ``right`` produces the new goal ``⊢ P``.

Note that when the goal contains an ``∨`` you have to choose between ``left`` and ``right``. Choose wisely!

Your turn.




If and only if
---------------

``P ↔ Q`` is just a short form for ``(P → Q) ∧ (Q → P)``. 
So you can use the tactics for ``→`` and ``∧`` when dealing with if and only if statements. 

.. code:: lean 

  -- P is a proposition 
  variables P Q:Prop

  --BEGIN--
  -- (P or Q) if and only if (Q or P).
  example : P ∨ Q ↔ Q ∨ P :=      
  begin 
    sorry, 
  end 
  --END--






Forward and backward reasoning 
-------------------------------

In math, it is we can either argue forwards or backwards. This is achieved in Lean using the ``have`` and ``apply`` tactic.

**Forward reasoning**
If one of the assumptions is ``hp : P`` and we know that ``hpq : P → Q`` then we can create an element ``hq : Q`` using the set of commands, 

.. code:: 
  
  have hq := hpq (hp),

There are more complicated ways of using the ``have`` tactic which we'll see later.



**Backward reasoning**
If the goal is ``⊢ Q`` and you know that ``hpq : P → Q`` then it suffices to show ``P``. This is achieved in Lean using the tactic:

.. code:: 
  
  apply f,

Try out the following using some combination of ``have`` and ``apply``.


.. code:: lean 

  -- P is a proposition 
  variables P Q R S T:Prop

  --BEGIN--
  -- if P and (P implies Q) and (Q implies R) and (R implies T) then T
  example 
    (hp : P)
    (hpq : P → Q)
    (hqr : Q → R)
    (hsr : S → R)
    (hrt : R → T) : T :=
    begin
      sorry,
    end
  --END--







.. Rewrite (rw) tactic 
.. ----------------------

.. The rewrite tactic is the way to "substitute in" the value
.. of a variable. In general, if you have a hypothesis of the form ``A = B``, and your
.. goal mentions the left hand side ``A`` somewhere, then
.. the ``rewrite`` tactic will replace the ``A`` in your goal with a ``B``.
.. Below is a theorem which cannot be
.. proved using ``refl`` -- you need a rewrite first.

.. Delete the sorry and take a look in the top right box at what we have.
.. The variables ``x`` and ``y`` are natural numbers, and we have
.. a proof ``h`` that ``y = x + 7``. Our goal
.. is to prove that ``2y=2(x+7)``. This goal is obvious -- we just
.. substitute in ``y = x + 7`` and we're done. In Lean, we do
.. this substitution using the ``rw`` tactic. So start your proof with 

.. .. code::

..     rw h,

.. and then hit enter. **Don't forget the comma.**
.. Did you see what happened to the goal? The goal doesn't close,
.. but it *changes* from ``⊢ 2 * y = 2 * (x + 7)`` to ``⊢ 2 * (x + 7) = 2 * (x + 7)``.
.. We can just close this goal with

.. .. code::

..     refl,

.. by writing it on the line after ``rw h,``. Don't forget the comma, hit
.. enter, and enjoy seeing the "Proof complete!" message in the
.. top right window. The other reason you'll know you're
.. done is that the bottom right window (the error window)
.. becomes empty. 


.. .. code:: lean 
    
..     lemma example2 
..       (x y : ℕ) 
..       (h : y = x + 7) 
..         : 2 * y = 2 * (x + 7) :=
..     begin 
..       sorry,
..     end





.. Left / Right tactic 
.. -------------------

.. ``P ∨ Q`` means ``P or Q``. So to prove it, you
.. need to choose one of ``P`` or ``Q``, and prove that one.
.. If ``⊢ P ∨ Q`` is your goal, then ``left`` changes this
.. goal to ``⊢ P``, and ``right`` changes it to ``⊢ Q``.
.. Note that you can take a wrong turn here. Let's
.. start with trying to prove ``Q → (P ∨ Q)``.
.. After the ``intro``, one of ``left`` and ``right`` leads
.. to an impossible goal, the other to an easy finish.

.. .. If $P$ and $Q$ are true/false statements, then $$Q\implies(P\lor Q).$$ 

.. .. code:: lean 

..   example (P Q : Prop) : Q → (P ∨ Q) :=
..   begin
..     sorry,
..   end



Practice exercises 
-------------------

.. code:: lean 

  variables p q r : Prop

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := sorry
  example : p ∨ q ↔ q ∨ p := sorry

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ false ↔ p := sorry
  example : p ∧ false ↔ false := sorry
  example : (p → q) → (¬q → ¬p) := sorry





Negation and LEM
===========================================
There is a false proposition ``false : Prop``, with no proof. 
One can check that ``¬ P`` is equivalent to ``P → false``. (Why?)

.. code:: lean
  :name: contrapositive

  variables P Q : Prop 

  --BEGIN--

  lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
  begin
    sorry,
  end

  --END--




Contrapose! tactic 
------------------
Proof by contrapositive is so common in math that there is a special tactic for this.

.. code:: 

  contrapose!,

Try the previous exercise by first applying ``intro hpq,`` and then ``contrapose!,``



Exfalso tactic 
---------------
It's certainly true that ``P ∧ (¬P) → Q`` for any propositions ``P`` and ``Q``,
because the left hand side of the implication is false. But how do we prove that false implies any proposition 
``Q``? A cheap way of doing it in Lean is using the ``exfalso`` tactic, which changes any goal at all to false. 

.. Lemma If  P and Q are true/false statements, then P ∧ (¬P) → Q

.. code:: lean 

  lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
  begin
    sorry,  
  end



By_contradiction tactic 
-----------------------
We proved earlier that ``(P → Q) → (¬ Q → ¬ P)``. The converse,
that ``(¬ Q → ¬ P) → (P → Q)`` is certainly true, but trying to prove
it using what we've learnt so far is impossible (because it is not provable in
constructive logic). 

But you can just prove this, and any other basic lemmas of this form like ``¬ ¬ P → P``,
using the ``by_cases`` tactic. Instead of starting with all the ``intro`` s, try this instead:

.. code:: 
  
  by_cases p : P,
  by_cases q : Q,

After it, there are four goals, one for each of the four possibilities ``PQ=TT, TF, FT, FF``.
You can see that ``p`` is a proof of ``P`` in some of the goals, and a proof of ``¬ P`` in others.
Similar comments apply to ``q``. 

This approach assumed that ``P ∨ ¬ P`` was true; the ``by_cases`` tactic just does ``cases`` on
this result. This is called the **law of the excluded middle**, and it cannot be proved using other axioms of logic.


.. If $P$ and $Q$ are true/false statements, then $$(\lnot Q\implies \lnot P)\implies(P\implies Q).$$ 

.. code:: lean 

  lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
  begin
    sorry,
  end 










First order logic 
=================


Use tactic 
----------



For all quantifier 
------------------




Exercises 
===========

Triple negation without LEM
---------------------------
This exercise follows directly from classical.not_not. 
However, classical.not_not introduces axioms that we don't need for this question.
Can you do this in tactic mode with only intro, apply, and exact?

.. code:: lean 
   :name: triple_negation

    theorem (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
    begin
      intro nnnp,
    end
    

Lounge paradox (a better name would be nice) 
--------------------------------------------
There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. code:: lean 
   :name: lounge_paradox

    theorem lounge {α : Type u} (r : α → Prop) [nonempty α] :
      ∃ x, (r x → ∀ y, r y) := 
    begin
      sorry
    end
