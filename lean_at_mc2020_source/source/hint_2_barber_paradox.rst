.. _hint_2_barber_paradox:

Hint 2 for the barber paradox
-----------------------------------

Try

.. code:: 
  
    by_contradiction,
    have b := a(barber),
    cases b with b1 b2,
    by_cases shaves barber barber,
