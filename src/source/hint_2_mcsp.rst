.. _hint_2_mcsp:

Hint 2 for the math campers singing paradox
--------------------------------------------

Try 

.. code:: 
  
  by_cases (∃ bob : camper, ¬ singing bob),
  cases h with bob key,
  use bob,
  push_neg at h,
