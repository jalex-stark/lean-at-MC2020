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

    lemma example1 (x y z : mynat) : x * y + z = x * y + z :=
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
      (x y : mynat) 
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





Cases tactic 
-------------




Split tactic
-------------




Left / Right tactic 
-------------------





Negation in Lean 
-----------------





First order logic 
=================



Unfold tactic 
-------------


Use tactic 
----------



For all quantifier 
------------------




Exercises 
===========


Lounge paradox (a better name would be nice) 
------------------
  There is someone in the lounge such that, if they are playing a game, then everyone in the lounge is playing a game.

.. code:: lean 

    theorem lounge {α : Type u} (r : α → Prop) [nonempty α] :
      ∃ x, (r x → ∀ y, r y) := sorry