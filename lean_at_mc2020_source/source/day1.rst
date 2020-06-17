.. _day1:

********
Basics 
********


Let's learn some tactics! Add a brief introduction to tactics.

Propositional Logic 
====================
A Proposition is a true/false statement, like ``2 + 2 = 4`` or ``2 + 2 = 5``.
Just like we can have concrete sets in Lean like ``ℕ``, and abstract
sets called things like ``X``, we can also have concrete propositions like
``2 + 2 = 5`` and abstract propositions called things like ``P``. 
The convention we'll use is capital letters for propositions and small letters for proofs. 


.. code:: 
    
    P : Prop
    p : P



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

Contrapose! tactic 
------------------



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
