


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
