import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


theorem duh (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  . rcases h with ⟨h1, h2⟩
    exact h2
  . exact h.1


theorem duh2 (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  . exact h.2
  . exact h.1

theorem duh3 (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  have right : p := by
    exact h.1
  constructor
  . exact h.2
  . exact right



theorem example_with_simp_all (p q r : Prop) :
  p → (p → q) → (q → r) → p ∧ r := by
  intro hp hpq hqr
  constructor
  · exact hp
  . exact hqr (hpq hp)



theorem duh' : ∃n:ℕ, 2+3 = n := by
  constructor
  simp
  -- case h
-- ⊢ 5 = ?w
-- case w
-- ⊢ ℕ
  case w => use 5
  rfl



-- Every morning Aya goes for a $9$-kilometer-
-- long walk and stops at a coffee shop afterwards.
--  When she walks at a constant speed of $s$ kilometers per
--  hour, the walk takes her 4 hours, including $t$ minutes
--  spent in the coffee shop. When she walks $s+2$ kilometers
--  per hour, the walk takes her 2 hours and 24 minutes,
--  including $t$ minutes spent in the coffee shop. Suppose
--  Aya walks at $s+\frac{1}{2}$ kilometers per hour. Find the
--  number of minutes the walk takes her, including the $t$ minutes
--  spent in the coffee shop.
-- Let's formalize the problem:
-- s is Aya's initial walking speed in km/h
-- t is the time spent in the coffee shop in minutes
-- d is the distance of the walk (9 km)



def walkProblem (s : ℚ) (t : ℚ) (d : ℚ) : Prop :=
  -- First scenario: speed s, total time 4 hours including t minutes in coffee shop
  d / s * 60 + t = 4 * 60 ∧
  -- Second scenario: speed s+2, total time 2h24m including t minutes in coffee shop
  d / (s + 2) * 60 + t = 2 * 60 + 24 ∧
  -- We want to find: time taken when speed is s+1/2, including t minutes
  d / (s + 1/2) * 60 + t = sorry

-- Solving this problem algebraically:
theorem solveWalkProblem :
  ∃ (s t : ℚ), walkProblem s t 9 ∧ (9 / (s + 1/2) * 60 + t = 180) := by
  unfold walkProblem
