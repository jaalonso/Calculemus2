import Mathlib.Tactic

example : 2 + 2 = 5 → 0 = 1 :=
by tauto

example : 2 + 2 = 5 → (∀ n, n > 2 → ¬∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^n + y^n ≠ z^n) :=
by tauto

example : 2 + 2 = 5 → (∀ n,  n > 2 → Even n → ∃ p q : ℕ, Prime p ∧ Prime q ∧ n = p + q) :=
by tauto
