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



Let's prove a simple statement.

.. code:: lean 
  :name: tautology

  -- P is a proposition 
  variables P : Prop

  -- if P is true then P is true.
  theorem tautology (hp : P) : P :=      
  begin 
    sorry, 
  end 


Here, we are saying given a proof ``hp:P`` produce a proof of ``P``. But that's just ``hp``! 
We tell Lean to use ``hp`` to "close the goal" by saying 

.. code:: 

  exact hp, 

Try replacing ``sorry`` with ``exact hp,`` in the above proof. 


Implies
-----------------------
Here's another way to describe the exact same statement. 

.. code:: lean 
  :name: tautology2

  -- P is a proposition 
  variables P : Prop


  -- P implies P
  theorem tautology2 : P → P :=      
  begin 
    sorry, 
  end 


Here, our goal is to produce a function ``f: P → P``. To do this, given an arbitrary proof ``hp:P`` we want to produce a proof of ``P``. To do this we use the ``intro`` tactic. Replace the ``sorry`` in the above proof with the following command.

.. code:: 

  intro hp,


How does this change the goal? Can you finish the proof now?





And 
----

If ``P`` and ``Q`` are proposition, then ``P ∧ Q`` is the proposition which is true precisely when both ``P`` and ``Q`` are true.


We need two tactics, ``cases`` and ``split``, to deal with ``∧`` depending on whether ``∧`` is in the assumptions or the goal.

1. If ``hpq : P ∧ Q`` is an assumption then writing ``cases hpq with hp hq,`` produces two new assumptions ``hp : P`` and ``hq : Q``.
2. If the current goal is ``⊢ P ∧ Q`` then the ``split,`` tactic produces two goals ``⊢ P`` and ``⊢ Q`` and Lean will then focus on one goal at a time.

Your turn.

.. code:: lean 

  -- P and Q are propositions
  variables P Q : Prop

  -- (P and Q) implies P.
  example : P ∧ Q → P :=      
  begin 
    sorry, 
  end 

  -- P implies (P and P).
  example : P → P ∧ P :=      
  begin 
    sorry, 
  end 

  -- (P and Q) implies (Q and P).
  example : P ∧ Q → Q ∧ P :=      
  begin 
    sorry, 
  end 






Or 
----


If ``P`` and ``Q`` are proposition, then ``P ∨ Q`` is the proposition which is true precisely when at least one of ``P`` and ``Q`` is true.


We need three tactics, ``cases``, ``left``, and ``right``, to deal with ``∨`` depending on whether ``∨`` is in the assumptions or the goal.

1. If ``hpq : P ∨ Q`` is an assumption then writing ``cases hpq with hp hq,`` breaks up the problem into two cases: one with the assumption ``hp : P`` and another with the assumption ``hq : Q``.
2. If the current goal is ``⊢ P ∨ Q`` then you have to make a choice of whether to prove ``P`` or ``Q``. You do this using either the ``left`` tactic or the ``right`` tactic.

Your turn.

.. code:: lean 

  -- P and Q are propositions 
  variables P Q:Prop

  -- P implies (P or Q).
  example : P → P ∨ Q :=      
  begin 
    sorry, 
  end 

  -- (P or P) implies P.
  example : P ∨ P → P :=      
  begin 
    sorry, 
  end 

    -- (P or Q) implies (Q or P).
  example : P ∨ Q → Q ∨ P :=      
  begin 
    sorry, 
  end 



If and only if
---------------

``P ↔ Q`` is just a short form for ``(P → Q) ∧ (Q → P)``. 
So you can use the tactics for ``→`` and ``∧`` when dealing with if and only if statements. 

.. code:: lean 

  -- Let P be a Proposition. 
  -- P is true if and only if (P or P) is true.
  example (P : Prop) : P ↔ P ∨ P :=      
  begin 
    sorry, 
  end 







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
  
  apply hpq,

Try out the following using some combination of ``have`` and ``apply``.


.. code:: lean 

  -- P Q R S T are propositions
  variables P Q R S T:Prop

  --BEGIN--
  -- if P and (P implies Q) and (Q implies R) and (S implies R) and (R implies T) then T
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
    
..     theorem example2 
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





Negation 
===========================================
There is a false proposition ``false : Prop``, with no proof. 
One can check that ``¬ P`` is equivalent to ``P → false``. (Why?)

.. code:: lean
  :name: contrapositive

  -- needed for using the contrapose! tactic
  import tactic 

  -- P Q are propositions 
  variables P Q : Prop 

  --BEGIN--

  -- (P implies Q) implies (not P implies not Q)
  theorem contrapositive : (P → Q) → (¬ Q → ¬ P) :=
  begin
    sorry,
  end

  --END--




Contrapositive  
------------------
Proof by contrapositive is so common in math that there is a special tactic for this.

.. code:: 

  contrapose!,

Try the previous exercise by first applying ``intro hpq,`` and then ``contrapose!,``
What if you start your proof with ``contrapose!``?







Proof by contradiction 
-----------------------
The converse, that ``(¬ Q → ¬ P) → (P → Q)`` is not provable using constructive logic and requires proof by contradiction. 
For this we need to use *proof by contradiction*. 

.. code:: 

  by_contradiction,

Try proving the following using proof by contradiction. 

.. code:: lean
  :name: contrapositive2

  -- needed for using the contrapose! tactic
  import tactic 

  -- P Q are propositions 
  variables P Q : Prop 

  --BEGIN--

  -- (P implies Q) implies (not P implies not Q)
  theorem contradiction : (¬ Q → ¬ P) → (P → Q) :=
  begin
    sorry,
  end

  --END--



Law of excluded middle
-----------------------
Often in math, we want to make statements like either ``P`` is true or ``¬ P`` is true. This is called the **law of excluded middle**. LEM is what makes proofs by contradiction work. To invoke LEM in Lean, we use the tactic ``by_cases p : P,`` where ``P : Prop`` is a proposition, which breaks the problem into two sub-problems one with the assumption ``hp : P`` and another with the assumption `` hnp : ¬ P``.

For  which of the following do you need to use the LEM? 

.. code:: lean 

  theorem LEM_1 (P : Prop) : P → ¬ ¬ P:=
  begin
    sorry,
  end 
  
  theorem LEM_2 (P : Prop) : ¬ ¬ P → P:=
  begin
    sorry,
  end 

  


Principle of explosion 
-----------------------
``P`` and  ``¬P`` implies anything. This is called the **principle of explosion** ("ex falso (sequitur) quodlibet = from falsehood, anything"). 
This is done in Lean using the ``exfalso`` tactic, which simply converts the current goal to ``false``. Give it a try.

.. code:: lean 
  :name: explosion

  -- P and not P implies Q
  theorem explosion (P Q : Prop) (P ∧ ¬ P) : Q :=
  begin
    sorry,  
  end



Practice exercises
-------------------

.. code:: lean 

  variables p q r s : Prop

  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry


First order logic 
=================



For all 
------------------
We need two tactics, ``intro`` and ``specialize``, for dealing with "∀" depending on whether it is in the assumptions or the goal.

1. If one of the assumptions is ``hp : ∀ x: X, P x`` and ``y : X`` then ``specialize hp y`` changes the assumption to ``hp : P y``.
2. If the current goal is ``⊢ ∀ x : X, P x`` then ``intro x`` produces an assumption ``x : X`` and changes the goal to ``P x``.

Your turn.

.. code:: lean 

  -- for all propositions P, (P and P) implies P
  example : ∀ P : Prop, (P ∧ P → P) :=
  begin 
    sorry,
  end     

  -- P is a collection of propositions, one for each natural number 
  variables (P : ℕ → Prop)

  example : (∀ x : ℕ, P x) → (∀ x : ℕ, P x) ∧ (∀ x : ℕ, P x) := 
  begin 
    sorry,
  end 

There exists 
-------------
We need two tactics, ``cases`` and ``use``, for dealing with "∃" depending on whether it is in the assumptions or the goal.

1. If one of the assumptions is ``hp : ∃ x: X, P x`` then ``cases hp with x hpx`` will produces two new assumptions ``x : X`` and ``hpx : P x``.
2. If the current goal is ``⊢ ∃ x : X, P x`` and ``y : X`` is one of the assumptions then ``use x,`` changes the goal to ``P y``. 

Your turn.

.. code:: lean 


  -- P is a collection of propositions, one for each natural number 
  variables (P : ℕ → Prop)

  example : (∀ x : ℕ, ¬ P x) ↔ ¬(∃ x : ℕ, P x) := 
  begin 
    sorry,
  end 




Problems 
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
    
   

Lounge paradox 
--------------------------------------------
There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. code:: lean 
   :name: lounge_paradox

    import tactic
    -- the next two lines let us use the by_cases tactic without trouble
    noncomputable theory
    open_locale classical 

    theorem lounge 
     {camper : Type u} (playing : camper → Prop) [inhabited camper] :
    ∃ x, (playing x → ∀ y, playing y) :=c
    begin
      have alice := arbitrary camper, -- this works because of "inhabited" above
      by_cases h : ∃ bob, ¬ playing bob,
    end

Odds and evens
---------------
Here's an example with statements about natural numbers. 
We started the proof by rewriting with something from the library. 
Try finishing the proof with just your logic tools --- you shouldn't need to know how natural numbers are implemented.

.. code:: lean 
   :name: odds_and_evens

    import tactic
    import data.nat.parity

    lemma even_of_odd_add_odd
      {a b : ℕ} (ha : ¬ nat.even a) (hb : ¬ nat.even b) :
    nat.even (a + b) :=
    begin
      rw nat.even_add,
    end