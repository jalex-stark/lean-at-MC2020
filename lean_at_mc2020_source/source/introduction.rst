.. _introduction:

Introduction
============

Getting Started
---------------

Every once in a while, you will see a code snippet like this:

.. code-block:: lean

    #eval "Hello, World!"

Clicking on the ``try it!`` button in the upper right corner will
open a copy in a window
so that you can edit it,
and Lean provides feedback in the ``Lean Goal`` window.
This book provides lots of challenging exercises for you to do that
way.

.. TODO: delete this, or update it

.. You can save your changes from VS Code in the usual way, and come back to the
.. same file by pressing the corresponding ``try it!`` button again.

.. If you want to reset the snippet or exercise to the version in the book,
.. simply delete or rename the file with the changes you have made,
.. and then press ``try it!`` once again.

.. Sometimes in the text we will quote from a longer example, like so:

.. .. code-block:: lean

..     -- Give an example here
..     -- Instead of a ``try it!'' button,
..     -- there should be a ``see more!`` button.

.. In that case, clicking on the ``see more!`` button opens a longer Lean file
.. and takes you to that line.
.. These displays are read only,
.. and you should think of them as part of the main text.
.. This allows us to describe a long development one piece at a time,
.. leaving you free to survey the whole development as you please.

.. Of course, you can create other Lean files to experiment.
.. We have therefore set up the main folder with four subdirectories:

.. * `snippets` contains your edited copies of the snippets in the text.

.. * `exercises` contains your edited copies of the exercises.

.. * `examples` contains the read-only examples we make use of in the text.

.. * `user` is a folder for you use any way you please.

Overview
--------

Put simply, Lean is a tool for building complex expressions in a formal language
known as *dependent type theory*.
Every expression has a *type*.
Some expressions have types like `ℕ` or `ℕ → ℕ`.
These are mathematical objects.

.. code-block:: lean

    #check 2 + 2

    def f (x : ℕ) := x + 3

    #check f

Some expressions have type `Prop`.
These are mathematical statements.

.. code-block:: lean

    #check 2 + 2 = 4

    def fermat_last_theorem :=
      ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

    #check fermat_last_theorem

Some expressions have a type, `P`, where `P` itself has type `Prop`.
Such an expression is a proof of the proposition `P`.

.. code-block:: lean

    def fermat_last_theorem :=
      ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

    -- BEGIN
    theorem easy : 2 + 2 = 4 := rfl

    #check easy

    theorem hard : fermat_last_theorem := sorry

    #check hard
    -- END

If you manage to construct an expression of type `fermat_last_theorem` and
Lean accepts it as a term of that type,
you have done something very impressive.
(Using ``sorry`` is cheating, and Lean knows it.)
So now you know the game.
All that is left to learn are the rules.


Interactive theorem proving can be frustrating,
and the learning curve is steep.
But the Lean community is very welcoming to newcomers,
and people are available on the `Lean Zulip chat group`_ round the clock
to answer questions.
We hope to see you there, and have no doubt that
soon enough you, too, will be able to answer such questions
and contribute to the development of *mathlib*.

So here is your mission, should you choose to accept it:
dive in, try the exercises, come to Zulip with questions, and have fun.
But be forewarned:
interactive theorem proving will challenge you to think about
mathematics and mathematical reasoning in fundamentally new ways.
Your life may never be the same.

*Acknowledgment.* 


**Further Reading.** 

#. `The Mechanization of Mathematics`_ 
#. `The Future of Mathematics`_
#. `Natural Number Game`_
#. mathlib_
#. `Natural Number Game`_
#. `mathlib repository`_
#. `Theorem Proving in Lean`_
#. `Lean Zulip chat group`_


.. _`The Mechanization of Mathematics`: https://www.ams.org/journals/notices/201806/rnoti-p681.pdf
.. _`The Future of Mathematics`: https://www.youtube.com/watch?v=Dp-mQ3HxgDE
.. _Lean: https://leanprover.github.io/people/
.. _mathlib: https://leanprover-community.github.io/
.. _`Natural Number Game`: https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/
.. _`mathlib repository`: https://github.com/leanprover-community/mathlib
.. _`Theorem Proving in Lean`: https://leanprover.github.io/theorem_proving_in_lean/
.. _`Lean Zulip chat group`: https://leanprover.zulipchat.com/
