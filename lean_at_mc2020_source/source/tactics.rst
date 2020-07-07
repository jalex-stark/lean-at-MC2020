.. _tactics:

*********************
Glossary of tactics 
*********************

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