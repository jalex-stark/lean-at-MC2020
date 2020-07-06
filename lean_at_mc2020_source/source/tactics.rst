.. _tactics:

*********************
Glossary of tactics 
*********************

Implications in Lean 
======================

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``exact``
     - If 
       ``P`` is the target of the current goal 
       and ``hp`` is a term of type ``P``,  
       then ``exact hp,`` will close the goal.

       Mathematically, this saying "this is *exactly* what we were required to prove".

   * - ``intro``
     - If the target of the current goal is a function ``P → Q``, 
       then ``intro hp,`` will produce a hypothesis 
       ``hp : P`` and change the target to  ``Q``.

       Mathematically, this is saying that in order to define a function from ``P`` to ``Q``,
       we first need to choose an arbitrary element of ``P``.

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``have``
     - ``have`` is used to create intermediate variables. 
     
       If ``f`` is a term of type ``P → Q`` and 
       ``hp`` is a term of type ``P``, then
       ``have hq := f(hp),`` creates the hypothesis ``hq : Q`` .
     
   * - ``apply``
     - ``apply`` is used for backward reasoning. 

       If the target of the current goal is ``Q`` and 
       ``f`` is a term of type ``P → Q``, then 
       ``apply f,`` changes target to ``P``.

       Mathematically, this is equivalent to saying "because ``P`` implies ``Q``, to prove ``Q`` it suffices to prove ``P``".

Proof by contradiction
========================

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``exfalso``
    - Changes the target of the current goal to ``false``.
      
      The name derives from `"ex falso, quodlibet" <https://en.wikipedia.org/wiki/Principle_of_explosion>`__ which translates to "from contradiction, anything". 
      You should use this tactic when there are contradictory hypotheses present. 
  
  * - ``by_cases``
    - If ``P : Prop``, then ``by_cases P,`` creates two goals, 
      the first with a hypothesis ``hp: P`` and second with a hypothesis ``hp: ¬ P``.

      Mathematically, this is saying either ``P`` is true or ``P`` is false.
      ``by_cases`` is the most direct application of the law of excluded middle.

  * - ``by_contradiction``
    - If the target of the current goal is  ``Q``,
      then ``by_contradiction,`` changes the target to  ``false`` and 
      adds ``hnq : ¬ Q`` as a hypothesis.

      Mathematically, this is proof by contradiction. 
  
  * - ``push_neg``
    - ``push_neg,`` simplifies negations in the target. 
    
      For example, if the target of the current goal is ``¬ ¬ P``, then 
      ``push_neg,`` simplifies it to ``P``. 

      You can also push negations across a hypothesis ``hp : P`` using ``push_neg at hp,``.

  * - ``contrapose!``
    - If the target of the current goal is  ``P → Q``,
      then ``contrapose!,`` changes the target to  ``¬ Q → ¬ P``.

      If the target of the current goal is ``Q`` 
      and one of the hypotheses is ``hp : P``,
      then ``contrapose! hp,`` changes the target to  ``¬ P`` 
      and changes the hypothesis to ``hp : ¬ Q``.

      Mathematically, this is replacing the target by its contrapositive.


Logical Operators
===================

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - ``cases`` is a general tactic that breaks a complicated term into simpler ones.

      If ``hpq`` is a term of type ``P ∧ Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``.

      If ``hpq`` is a term of type ``P × Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``. 

      If ``hpq`` is a term of type ``P ↔ Q``, then 
      ``cases fg with f g,`` breaks it into ``f : P → Q`` and ``g : Q → P``.

      If ``hpq`` is a term of type ``P ∨ Q``, then 
      ``cases hpq with hp hq,`` creates two goals and adds the hypotheses ``hp : P`` and ``hq : Q`` to one each.

  * - ``split``
    - If the target of the current goal is ``P ∧ Q``, then 
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
