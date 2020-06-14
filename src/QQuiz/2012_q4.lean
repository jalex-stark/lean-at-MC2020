import tactic
import data.real.basic

noncomputable theory
open_locale classical

-- Let a be a rational number with 0 < a < 1. 
-- A lollipop in the xy-plane with base (a,0) consists of 
---- a line segment from (a,0) to some point (a,b) with b > 0, 
---- together with a filled in disc of radius less than b, centered at (a,b). 

def lollipop (a b r : ℝ) (hb : 0 < b) (hr : r < b) : set ℝ :=
begin

end

-- Determine whether or not it is possible to have a set of lollipops in the xy-plane satisfying both of the following conditions:
-- for every rational number a with 0 < a < 1, there is a lollipop whose base is the point (a,0),
-- no two lollipops touch or overlap each other.
-- If such a set of lollipops exists, explain how to construct it. If not, justify why not.