import data.nat.basic
import data.nat.parity
import data.int.basic
import data.equiv.denumerable
import tactic


lemma frog_explicit_formula
{frog : ℕ → ℤ}
{step : ℤ}
{start : ℤ}
(frog_0 : frog 0 = start) 
(frog_step : ∀ n, frog (n+1) = frog n + step)
(n : ℕ)
:
frog n = start + n * step := begin
induction n with d hd,
rw frog_0, norm_num,
rw [frog_step, hd, ←nat.add_one],
ring, ring,
end


def int_sq_enum_inv : ℤ × ℤ → ℕ := encodable.encode

open denumerable


def strategy_c (n : ℕ): ℤ := (of_nat (ℤ × ℤ) n).fst + n * (of_nat (ℤ × ℤ) n).snd
theorem part_c 
(frog : ℕ → ℤ) 
-- It starts somewhere, let's call that` start`
(start : ℤ) 
(frog_start : frog 0 = start) 
-- the same positive integer n each time)
(step : ℤ) 
-- every second it jumps n units to the right. 
(frog_step : ∀ n, frog (n+1) = frog n + step) :
∃n, frog n = (strategy_c n) := 
begin
-- use encodable.encode ⟨start, step⟩,
use int_sq_enum_inv ⟨start, step⟩,
unfold strategy_c, unfold int_sq_enum_inv,

rw denumerable.of_nat_encode, simp only [],

rw frog_explicit_formula frog_start frog_step,
end
