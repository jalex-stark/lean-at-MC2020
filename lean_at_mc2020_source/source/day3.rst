.. _day3:

***************************
Type classes and instances
***************************


Many technical lemmas 
=====================


.. code-block:: lean
   :name: two_dvd_of_two_dvd_sq

    lemma two_dvd_of_two_dvd_sq (m n : ℕ) : 2 * m^2 = n^2 → 2 ∣ n :=
    begin
      intros eq₁,
      have : 2 ∣ n^2, by { use m^2, exact eq.symm eq₁},
      exact nat.prime.dvd_of_dvd_pow nat.prime_two ‹2 ∣ n^2 ›,
    end

.. code-block:: lean
   :name: gcd_div_left

    lemma gcd_div_left (a b : ℕ) : (nat.gcd a b) ∣ a :=
    begin
      simp [nat.gcd_eq_right_iff_dvd],
    end

.. code-block:: lean
   :name: gcd_div_right

    lemma gcd_div_right (a b : ℕ) : (nat.gcd a b) ∣ b :=
    begin
      rw nat.gcd_comm, apply gcd_div_left,
    end

.. code-block:: lean
   :name: eq_zero_of_sq_eq_zero

    lemma eq_zero_of_sq_eq_zero (m : ℕ) : m^2 = 0 → m = 0 :=
    begin
      simp [nat.pow_two, nat.mul_eq_zero], 
    end

.. code-block:: lean
   :name: sq_eq_zero_iff_eq_zero

  lemma sq_eq_zero_iff_eq_zero (m : ℕ) : m^2 = 0 ↔ m = 0 :=
  begin
    split, { apply eq_zero_of_sq_eq_zero },
    sorry
  end