import Mathlib.Tactic
variable (P Q R : Prop)

-- 1ª demostración
example
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by
  have hQ : Q := And.right hPQ
  show Q ∧ R
  exact And.intro hQ hR

-- 2ª demostración
example
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by
  have hQ : Q := hPQ.2
  show Q ∧ R
  exact ⟨hQ, hR⟩

-- 3ª demostración
example
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
⟨hPQ.2, hR⟩
