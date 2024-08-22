-- Composicion_de_funciones_monotonas.lean
-- La composición de dos funciones monótonas es monótona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones monótonas es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean f y g dos funciones monótonas de ℝ en ℝ. Tenemos que demostrar
-- que f ∘ g es monótona; es decir, que
--    (∀ a, b ∈ ℝ) [a ≤ b → (f ∘ g)(a) ≤ (f ∘ g)(b)]
-- Sean a, b ∈ ℝ tales que a ≤ b. Por ser g monótona, se tiene
--    g(a) ≤ g(b)
-- y, por ser f monótona, se tiene
--    f(g(a)) ≤ f(g(b))
-- Finalmente, por la definición de composición,
--    (f ∘ g)(a) ≤ (f ∘ g)(b)
-- que es lo que había que demostrar.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- 1ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f ∘ g) :=
by
  have h1 : ∀ a b, a ≤ b → (f ∘ g) a ≤ (f ∘ g) b := by
  { intros a b hab
    have h1 : g a ≤ g b := mg hab
    show (f ∘ g) a ≤ (f ∘ g) b
    exact mf h1 }
  show Monotone (f ∘ g)
  exact h1

-- 2ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f ∘ g) :=
by
  have h1 : ∀ a b, a ≤ b → (f ∘ g) a ≤ (f ∘ g) b := by
  { intros a b hab
    show (f ∘ g) a ≤ (f ∘ g) b
    exact mf (mg hab) }
  show Monotone (f ∘ g)
  exact h1

-- 3ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f ∘ g) :=
by
  -- a b : ℝ
  -- hab : a ≤ b
  intros a b hab
  -- (f ∘ g) a ≤ (f ∘ g) b
  apply mf
  -- g a ≤ g b
  apply mg
  -- a ≤ b
  apply hab

-- 4ª demostración
example (mf : Monotone f) (mg : Monotone g) :
  Monotone (f ∘ g) :=
λ _ _ hab ↦ mf (mg hab)
