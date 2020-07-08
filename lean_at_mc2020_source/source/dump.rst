Mathematical Induction 
========================


.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``induction``
    - If ``n : ℕ`` is a hypothesis and the target of the current goal is a proposition 
      ``⊢ P(n)`` that depends on ``n``,  
      then ``induction n with d hd,`` removes the hypothesis ``n : ℕ`` produces breaks down the current goal into two goals:
      
      * the first with target ``⊢ P(0)`` 
      * the second with two added hypotheses ``d : ℕ`` and ``hd : P(d)`` and target ``⊢ P(d.succ)``.

      This is precisely the statement of mathematical induction. 


.. code:: lean 

  def f : ℕ → ℕ
  | 0 := 0
  | (n + 1) := n + 1 + f n

  example : f 1 = 1 := 
  begin
    unfold f,
  end

  example (n : ℕ) : 2 * f n = n * (n + 1) :=
  begin
    induction n with d hd,  
    -- base case
    { unfold f, simp },
    rw nat.succ_eq_add_one,
    unfold f, ring, 
    rw hd, ring,
  end
