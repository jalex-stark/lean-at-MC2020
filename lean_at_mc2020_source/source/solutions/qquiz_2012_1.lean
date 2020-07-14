import data.nat.basic
import data.nat.parity
import data.int.basic
import tactic

@[ext]
structure frog :=
  -- A frog hangs out on the natural number line of lily pads
  (location : ℕ → ℕ)
  -- At time 0, it sits on location 0
  (location_zero : location 0 = 0) 
  -- For some fixed step size, 
  (step_size : ℕ)
  -- the frog jumps `step_size` units to the right each second.
  (step : ∀ n, location (n+1) = location n + step_size)

lemma frog_explicit_formula (f : frog) :
-- Show that the position of the frog at time n is n * step_size.
∀ n, f.location n = n * f.step_size := 
begin
  intros, induction n with d hd,
  rw f.location_zero, norm_num,
  rw [f.step, hd, ← nat.add_one],
  ring,
end

-- We can define a frog just by giving its step size
local attribute [simp]
def frog_of_step_size (step_size : ℕ) : frog :=
{ location := λ n, n * step_size, 
  location_zero := by simp, 
  step_size := step_size, 
  step := by {intro, ring} }

-- and every frog can be defined in this way
lemma frog_eq_frog_of_step_size (f : frog) : 
f = frog_of_step_size f.step_size :=
begin
  ext, 
  { rw frog_explicit_formula, simp },
  simp,
end

lemma catch_the_frog : 
-- Show that there is a way to check one lily pad each second
  ∃ (strategy : ℕ → ℕ), 
-- so that no matter how fast the frog travels,
  ∀ step_size, 
-- you'll eventually catch it. 
  ∃ catch_time > 0, 
  strategy catch_time = (frog_of_step_size step_size).location catch_time :=
begin
  use λ n, n * (n - 1),
  intro k, use k + 1,
  split, { linarith, },
  simp,
end

