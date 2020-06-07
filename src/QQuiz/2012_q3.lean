import tactic
import data.nat.modeq

noncomputable theory
open_locale classical

-- Let p be an odd prime. 

variables {p : ℕ} [fact p.prime]

-- A group of p campers sit around a circle, 
-- and are labeled with the integers 1,2,...,p in clockwise order. 
-- The camper with label 1 yells out the number 1. 
-- The camper sitting next to this camper in clockwise order yells out 2. 
-- The camper two spots in clockwise order from the camper who yelled out 2 yells out 3. 
-- This process continues: the camper seated n spots (in clockwise order) from the camper who yelled out n must yell out n+1. 
-- A camper gets a cookie anytime she or he yells out a number.

lemma arithmetic1 (a b : ℕ) (hb : 1 < b) : a % b < b := sorry

structure camper_state (campers : Type*) :=
(head : campers)
(count : ℕ)
(cookies : campers → ℕ)

def initial_state : camper_state (fin p) := 
begin
  refine {head := _, count := 0, cookies := λ x, 0},
  refine ⟨1, _⟩, apply nat.prime.one_lt, assumption,
end

def update : camper_state (fin p) → camper_state (fin p) :=
begin
  intro s,
  refine {head := _, 
  count := s.count + 1, 
  cookies := λ x, if x = s.head then s.cookies x + 1 else s.cookies x
  },
  refine ⟨ (s.head + s.count) % p, _ ⟩, 
  apply arithmetic1, refine nat.prime.one_lt _inst_1,
end

def seq_state : ℕ → camper_state (fin p)
| 0 := initial_state
| (n+1) := update (seq_state n)

-- Show that there is a camper who never gets a cookie.
def sad_camper (a : fin p) : Prop := ∀ n, (seq_state n).cookies a = 0 :=
  
theorem exists_sad_camper : ∃ a : fin p, sad_camper a :=
  sorry

-- Of the campers who do get cookies, is there one who at some point has at least ten more cookies than the others?

def max_cookie_camper (a : fin p) : Prop := 
∀ n, ∀ b ≠ a, 10 < (seq_state n).cookies a - (seq_state n).cookies b
  
-- prove the following statement or its negation
theorem exists_max_cookie_camper : ∃ a : fin p, max_cookie_camper a :=
  sorry

-- Of the campers who do get cookies, is there one who at some point has at least ten fewer cookies than the others?

def min_cookie_camper (a : fin p) : Prop := 
∀ n, ∀ b ≠ a, sad_camper b ∨ 10 < (seq_state n).cookies b - (seq_state n).cookies a

-- prove the following statement or its negation
theorem exists_min_cookie_camper : ∃ a : fin p, min_cookie_camper a :=
  sorry

