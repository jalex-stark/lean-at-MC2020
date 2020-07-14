.. _symbols:


Pretty Symbols in Lean
=================================

To produce a pretty symbol in Lean, type the *editor shortcut* followed by space or tab. 

.. list-table::
  :widths: 20 35 45
  :header-rows: 1

  * - Unicode 
    - Editor Shortcut 
    - Definition 

  * - →
    - ``\to``
    - function or implies 
  
  * - ↔
    - ``\iff``
    - if and only if 

  * - ←
    - ``\l`` 
    - used by the ``rw`` tactic

  * - ¬
    - ``\not`` 
    - negation operator

  * - ∧
    - ``\and``
    - and operator
  
  * - ∨ 
    - ``\or``
    - or operator 

  * - ∃ 
    - ``\exists``
    - there exists quantifier 

  * - ∀
    - ``\forall``
    - for all quantifier

  * - ∣
    - ``\mid``
    - divisibility [#f1]_

  * - ℕ
    - ``\nat``
    - type of natural numbers

  * - ℤ
    - ``\int``
    - type of integers
  
  * - ∘
    - ``\circ``
    - composition of functions

  * - ≠
    - ``\ne``
    - not equal to


.. rubric:: Footnotes

.. [#f1] Be very careful! The symbol for divisibility is not the ``|`` symbol on your keyboard. Lean will through a cryptic error if you use it.