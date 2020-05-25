import data.nat.basic
import data.nat.parity
import data.int.basic
import data.equiv.denumerable
import data.int.modeq
import tactic


-- Determine all possible colorings of the integers that satisfy these rules.


structure coloring := 
-- Each integer on the number line is colored with exactly one of three possible colors—red, green or blue
(red green blue : set ℤ)
(total : ∀ n, red n ∨ blue n ∨ green n)
--according to the following two rules: 
-- the negative of a red number must be colored blue, 
(neg_red : ∀ n, red n → blue (-n))
--and the sum of two blue numbers (not necessarily distinct) must be colored red.
(add_blue : ∀ n m ∈ blue, n + m ∈ red)

-- Show that the negative of a blue number must be colored red 

lemma neg_blue (x : coloring) : ∀ n, x.blue n → x.red (-n) := begin
intros n hn, 
have calc1 := x.add_blue _ _ hn hn,
have calc2 := x.neg_red _ calc1,
have calc3 := x.add_blue _ _ hn calc2,
have calc4 : n + -(n + n) = (-n), ring,
rw calc4 at calc3, exact calc3,
end

-- and the sum of two red numbers must be colored blue.

lemma add_red (x : coloring) : ∀ n m ∈ x.red, n + m ∈ x.blue := 
begin
intros n m hn hm,
have calc1 := x.neg_red _ hn,
have calc2 := x.neg_red _ hm,
have calc3 := x.add_blue _ _ calc1 calc2,
have calc4 := x.neg_red _ calc3,
simp only [neg_add_rev, neg_neg] at calc4,
rw add_comm, exact calc4,
end

-- Determine all possible colorings of the integers that satisfy these rules.
#print notation ≡

-- if x is blue, then 2^n * x is blue when n is even and red when n is odd
-- so coloring behavior is determined by behavior on 2 and odd numbers
-- if 2 is blue and 1 is red, then all numbers 1 mod 4 are red and 3 mod 4 are blue

example : 3 - 5 = 0 := 
begin
norm_num,
end

example : (3 : ℤ) - 5 ≠ 0 := 
begin
norm_num,
end


lemma mod_four (x : coloring) (h1 : x.red 1) : ∀ n, x.red n ↔ n ≡ 1 [ZMOD 4] := begin

end

