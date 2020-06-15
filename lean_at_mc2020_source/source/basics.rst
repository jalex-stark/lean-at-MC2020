.. _basics:

********
Basics 
********


Tactics
========
Let's learn some tactics! Add a brief introduction to tactics.

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


Rewrite (rw) tactic 
----------------------

The rewrite tactic is the way to "substitute in" the value
of a variable. In general, if you have a hypothesis of the form ``A = B``, and your
goal mentions the left hand side ``A`` somewhere, then
the ``rewrite`` tactic will replace the ``A`` in your goal with a ``B``.
Below is a theorem which cannot be
proved using ``refl`` -- you need a rewrite first.

Delete the sorry and take a look in the top right box at what we have.
The variables ``x`` and ``y`` are natural numbers, and we have
a proof ``h`` that ``y = x + 7``. Our goal
is to prove that ``2y=2(x+7)``. This goal is obvious -- we just
substitute in ``y = x + 7`` and we're done. In Lean, we do
this substitution using the ``rw`` tactic. So start your proof with 

.. code::

    rw h,

and then hit enter. **Don't forget the comma.**
Did you see what happened to the goal? The goal doesn't close,
but it *changes* from ``⊢ 2 * y = 2 * (x + 7)`` to ``⊢ 2 * (x + 7) = 2 * (x + 7)``.
We can just close this goal with

.. code::

    refl,

by writing it on the line after ``rw h,``. Don't forget the comma, hit
enter, and enjoy seeing the "Proof complete!" message in the
top right window. The other reason you'll know you're
done is that the bottom right window (the error window)
becomes empty. 


.. code:: lean 
    
    lemma example2 
      (x y : ℕ) 
      (h : y = x + 7) 
        : 2 * y = 2 * (x + 7) :=
    begin 
      sorry,
    end



Intro tactic 
-------------
If your goal is a function or an implication ``⊢ P → Q`` then ``intro``
will always make progress. ``intro p`` turns

``⊢ P → Q``

into 

.. code:: 
  
    p : P
    ⊢ Q

What does it mean to define
a function? Given an arbitrary term of type ``P`` you need
to come up with a term of type ``Q``, so your first step is
to choose ``p``, an arbitrary element of ``P``. 

``intro p,`` is Lean's way of saying "let `p` be an arbitrary element of `P`.
The tactic ``intro p`` changes

.. code:: 
  
    ⊢ P → Q

into


.. code:: 
    
    p : P
    ⊢ Q

So ``p`` is an arbitrary element of ``P`` about which nothing is known,
and our task is to come up with an element of ``Q`` (which can of
course depend on ``p``).



Propositional Logic 
====================
A Proposition is a true/false statement, like ``2 + 2 = 4`` or ``2 + 2 = 5``.
Just like we can have concrete sets in Lean like ``ℕ``, and abstract
sets called things like ``X``, we can also have concrete propositions like
``2 + 2 = 5`` and abstract propositions called things like ``P``. 
The convention we'll use is capital letters for propositions and small letters for proofs. 


.. code:: lean 
    
    P : Prop
    p : P



Exact tactic 
------------

We have types ``P`` and ``Q`` and inhabitant ``p`` of ``P`` (written ``p : P``). 
We also have a function ``h`` from ``P`` to ``Q``, and our goal is to construct an
element of the set ``Q``. It's clear what to do *mathematically* to solve
this goal -- we can
make an element of ``Q`` by applying the function $h$ to
the element $p$. But how to do it in Lean? 
You can just write ``exact <formula>`` and this will close the goal. 

**Example**

If your local context looks like this

.. code::

    P Q : Type,
    p : P,
    h : P → Q
    ⊢ Q


then ``h(p)`` is an inhabitant of ``Q`` so you can just write

.. code:: 

    exact h(p),

to close the goal. 



**Important note:** Note that ``exact h(P),`` won't work (with a capital ``P``). 
``P`` is not an inhabitant of ``P``, it's ``p`` that is an inhabitant of ``P``. 


.. code:: lean 

    example (P Q : Type) (p : P) (h : P → Q) : Q :=
    begin
      sorry,
    end



Apply tactic
------------


.. [diagram](https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game_images/function_diag.jpg)

.. image:: https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game_images/function_diag.jpg
   :width: 300


We are given ``p : P`` and our goal is to find an element of ``U``, or
in other words to find a path through the maze that links ``P`` to ``U``.
In level 3 we solved this by using ``have`` s to move forward, from P
to ``Q`` to ``T`` to ``U``. Using the ``apply`` tactic we can instead construct
the path backwards, moving from ``U`` to ``T`` to ``Q`` to ``P``.

Our goal is to construct an element of the set ``U``. But ``l:T → U`` is
a function, so it would suffice to construct an element of ``T``. Tell
Lean this by starting the proof below with

.. code:: 

  apply l,


and notice that our assumptions don't change but *the goal changes*
from ``⊢ U`` to ``⊢ T``. 

Keep ``apply``ing functions until your goal is ``P``, and try not
to get lost! Now solve this goal
with ``exact p``. 


.. Given an element of $P$ we can define an element of $U$.

.. code:: lean 

  example (P Q R S T U: Type)
  (p : P)
  (h : P → Q)
  (i : Q → R)
  (j : Q → T)
  (k : S → T)
  (l : T → U)
  : U :=
  begin
    sorry,
  end




Split tactic
-------------
The logical symbol ``∧`` means ``and``. If ``P`` and ``Q`` are propositions, then
``P ∧ Q`` is the proposition ``P and Q``. If your *goal* is ``P ∧ Q`` then
you can make progress with the ``split`` tactic, which turns one goal ``⊢ P ∧ Q``
into two goals, namely ``⊢ P`` and ``⊢ Q``. In the level below, after a ``split``,
you will be able to finish off the goals with the ``exact`` tactic.


.. If $P$ and $Q$ are true, then $P\land Q$ is true.

.. code:: lean 

  example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
  begin
    sorry,
  end 

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.


If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

**Example:**

If your local context (the top right window) looks like this

.. code:: 

  a b : ℕ,
  ⊢ a = b ↔ a + 3 = b + 3
  

then after

.. code:: 

  split,


it will look like this:

.. code:: 

  2 goals
  a b : ℕ
  ⊢ a = b → a + 3 = b + 3

  a b : ℕ
  ⊢ a + 3 = b + 3 → a = b




Cases tactic 
-------------
If ``P ∧ Q`` is in the goal, then we can make progress with ``split``.
But what if ``P ∧ Q`` is a hypothesis? In this case, the ``cases`` tactic will enable
us to extract proofs of ``P`` and ``Q`` from this hypothesis.

The lemma below asks us to prove ``P ∧ Q → Q ∧ P``, that is,
symmetry of the "and" relation. The obvious first move is

.. code:: 
  
  intro h,


because the goal is an implication and this tactic is guaranteed
to make progress. Now ``h : P ∧ Q`` is a hypothesis, and

.. code:: 
  
  cases h with p q,


will change ``h``, the proof of ``P ∧ Q``, into two proofs ``p : P``
and ``q : Q``. From there, ``split`` and ``exact`` will get you home.



.. If $P$ and $Q$ are true/false statements, then $P\land Q\implies Q\land P$. 

.. code:: lean 
  
  lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=
  begin
    sorry,
  end 




Left / Right tactic 
-------------------

``P ∨ Q`` means ``P or Q``. So to prove it, you
need to choose one of ``P`` or ``Q``, and prove that one.
If ``⊢ P ∨ Q`` is your goal, then ``left`` changes this
goal to ``⊢ P``, and ``right`` changes it to ``⊢ Q``.
Note that you can take a wrong turn here. Let's
start with trying to prove ``Q → (P ∨ Q)``.
After the ``intro``, one of ``left`` and ``right`` leads
to an impossible goal, the other to an easy finish.

.. If $P$ and $Q$ are true/false statements, then $$Q\implies(P\lor Q).$$ 

.. code:: lean 

  example (P Q : Prop) : Q → (P ∨ Q) :=
  begin
    sorry,
  end







Negation in Lean 
================
There is a false proposition ``false``, with no proof. It is
easy to check that ``¬ P`` is equivalent to ``P → false``,

.. code:: 

  not_iff_imp_false (P : Prop) : ¬ P ↔ (P → false)


So you can start the proof of the contrapositive below with

.. code:: 
  
  rw not_iff_imp_false,


.. If $P$ and $Q$ are propositions, and $P\implies Q$, then $\lnot Q\implies \lnot P$. 

.. code:: lean 

  lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
  begin
    sorry,
  end




Exfalso tactic 
---------------



By_contradiction tactic 
-----------------------



Contrapose and push_neg tactics
-------------------------------



First order logic 
=================

Unfold tactic 
---------------


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

    theorem (P : Prop) : ¬ ¬ ¬ P → ¬ P :=
    begin
      intro nnnp,
    end
    

Lounge paradox (a better name would be nice) 
--------------------------------------------
There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. code:: lean 

    theorem lounge {α : Type u} (r : α → Prop) [nonempty α] :
      ∃ x, (r x → ∀ y, r y) := 
    begin
      sorry
    end
