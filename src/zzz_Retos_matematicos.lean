import Mathlib.Tactic

example : 2 + 2 = 5 → 0 = 1 :=
by tauto

example : 2 + 2 = 5 → (∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n) :=
by tauto
