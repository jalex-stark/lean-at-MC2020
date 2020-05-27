import data.nat.basic
import data.nat.parity
import data.int.basic
import data.equiv.denumerable
import data.int.modeq
import tactic


-- Determine all possible colorings of the integers that satisfy these rules.


structure coloring := 
-- Each integer on the number line is colored with exactly one of three possible colors—red, green or blue
(red blue : set ℤ)
(disjoint : ∀ n, ¬(red n ∧ blue n) )
--according to the following two rules: 
-- the negative of a red number must be colored blue, 
(neg_red : ∀ n, red n → blue (-n))
--and the sum of two blue numbers (not necessarily distinct) must be colored red.
(add_blue : ∀ n m ∈ blue, n + m ∈ red)



example (n m : ℤ) : n ≡ 2 [ZMOD 3] → m ≡ 2 [ZMOD 3] → (n+m) ≡ 1 [ZMOD 3]:=
begin
exact int.modeq.modeq_add,
end


-- a nontrivial example of a coloring
def mod_3_coloring : coloring :=
begin
  refine {red := {x | x ≡ 1 [ZMOD 3]}, 
  blue := {x | x ≡ 2 [ZMOD 3]}, 
  disjoint := by {intros n hn, cases hn with h1 h2,
    have key : 1 ≡ 2 [ZMOD 3], transitivity n, symmetry, assumption',
    revert key,
    exact of_to_bool_ff rfl}, 
  neg_red := by {intro n, exact int.modeq.modeq_neg}, 
  add_blue := by {intros n m, exact int.modeq.modeq_add}},
end


-- Show that the negative of a blue number must be colored red 

lemma neg_blue {x : coloring} {n : ℤ} (hn : x.blue n) : x.red (-n) := begin
-- intros n hn, 
have calc1 := x.add_blue _ _ hn hn,
have calc2 := x.neg_red _ calc1,
have calc3 := x.add_blue _ _ hn calc2,
have calc4 : n + -(n + n) = (-n), ring,
rw calc4 at calc3, exact calc3,
end

-- and the sum of two red numbers must be colored blue.

lemma add_red {x : coloring} {n m : ℤ} (hn : x.red n) (hm : x.red m) : n + m ∈ x.blue := 
begin
-- intros n m hn hm,
have calc1 := x.neg_red _ hn,
have calc2 := x.neg_red _ hm,
have calc3 := x.add_blue _ _ calc1 calc2,
have calc4 := x.neg_red _ calc3,
simp only [neg_add_rev, neg_neg] at calc4,
rw add_comm, exact calc4,
end

-- Determine all possible colorings of the integers that satisfy these rules.

-- if x is blue, then 2^n * x is blue when n is even and red when n is odd
-- so coloring behavior is determined by behavior on 2 and odd numbers
-- if 2 is blue and 1 is red, then all numbers 1 mod 4 are red and 3 mod 4 are blue


lemma zero_green (x : coloring) : ¬ x.red 0 ∧ ¬ x.blue 0 :=
begin
split; intro, 
  have calc1 := x.neg_red _ a, 
  swap, have calc1 := neg_blue x _ a, 
all_goals {simp only [neg_zero] at calc1, apply x.disjoint 0, finish},
end

lemma reachable_from_one (x : coloring) (h1 : x.red 1) : false :=
begin
  have h2 := add_red x 1 1 h1 h1, norm_num at h2,
  -- get powers of two by induction
end

lemma powers_of_two {x : coloring} {n : ℤ} (hn : x.red n) (k : ℕ) : 
2^(2 * k) * n ∈ x.red ∧ 2 ^ (2 * k + 1) * n ∈ x.blue :=
begin
  induction k with k hk,
    {simp only [one_mul, pow_one, mul_zero, pow_zero],
    split, assumption,
    have key := add_red x _ _ hn hn, ring at key, exact key},
  suffices key : 2 ^ (2 * k.succ) * n ∈ x.red,
    {split, assumption,
    have calc1 := add_red x _ _ key key, 
    ring_exp at calc1, ring_exp, exact calc1},
  cases hk with _ hk,
    have calc1 := x.add_blue _ _ hk hk,
    rw ← nat.add_one, ring_exp, norm_num, ring_exp,
    ring_exp at calc1, exact calc1,
end

lemma red_sub_blue {x : coloring} {n m : ℤ} (hn : x.red n) (hm : x.blue m) :
x.blue (n - m) :=
begin
  have calc1 := neg_blue hm,
  have calc2 := add_red hn calc1,
  ring at calc2, exact calc2,
end


lemma blue_mul_3_not_red (x : coloring) (n : ℤ) (hn : x.blue n) (h3n : x.red (3*n)) : false :=
begin
  have key1 := red_sub_blue h3n hn, ring at key1,
  have key2 := x.add_blue _ _ hn hn, ring at key2,
  apply x.disjoint (2 * n), finish,
end

lemma red_mul_3_not_red (x : coloring) (n : ℤ) (hn : x.red n) (h3n : x.red (3*n)) : false :=
begin
  have h16n := (powers_of_two hn 2).left, norm_num at h16n,
  suffices h13n : x.red (13 * n),
    {have calc2 := add_red h13n h3n, ring at calc2,
    apply x.disjoint (16 * n), finish},
  have calc1 := powers_of_two hn 1, cases calc1 with h4n h8n, norm_num at h4n h8n,
  have h5n := add_red hn h4n, ring at h5n,
  have h13n := x.add_blue _ _ h5n h8n, ring at h13n, exact h13n,
end

lemma mul_3_not_red {x : coloring} {n : ℤ} (hn : n ≡ 0 [ZMOD 3]) (n_red : x.red n) : false :=
begin
  have calc1 : 3 ∣ n := int.dvd_of_mod_eq_zero hn,
  cases calc1 with k hk,
--   have calc1 : ∃ k, n = 3 * k, 
end

lemma one_mod_3_red_of_one_red {x : coloring} (h1 : x.red 1) (n : ℕ): 
x.red (3 * n + 1) ∧ x.blue (3 * n + 2) :=
begin
  have h2 := add_red h1 h1, ring at h2,
  induction n with k hk,
  { norm_num, split; assumption },
  suffices key : x.red (3 * ↑(k.succ) + 1),
    { split, assumption,
      have := add_red key h1, ring at this, exact this },
  have := x.add_blue _ _ hk.right h2, ring at this, 
  rw ← nat.add_one, norm_cast, ring, exact this,
end



-- p blue, q blue
-- 2q > p
-- p + q red
-- 2q red


-- a red number minus a blue number is a blue number

-- this reduces the problem to coloring the odd numbers


-- n is blue
-- 2n is red
-- 4n is blue
-- 5n is red
-- 8n is red
-- 7n is blue
-- 11n is red
-- 13n is blue

-- 3*n is red, n is blue, 
-- implies 2n is blue; contradiction

-- n is red, 4*n is red, 16*n is red,
-- 5*n is blue
-- 20*n is blue
-- -20*n is red
-- -4*n is blue
