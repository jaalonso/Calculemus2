-- Suma_de_funciones_monotonas.lean
-- Suma de funciones monótonas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de dos funciones monótonas es monótona.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usará el siguiente lema:
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--
-- Supongamos que f y g son monótonas y teneno que demostrar que f+g
-- también lo es; que
--    ∀ a b, a ≤ b → (f + g)(a) ≤ (f + g)(b)
-- Sean a, b ∈ ℝ tales que
--    a ≤ b                                                          (1)
-- Entonces, por ser f y g monótonas se tiene
--    f(a) ≤ f(b)                                                    (2)
--    g(a) ≤ g(b)                                                    (3)
-- Entonces,
--    (f + g)(a) = f(a) + g(a)
--               ≤ f(b) + g(b)    [por add_le_add, (2) y (3)]
--               = (f + g)(b)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

-- 1ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b := by
  { intros a b hab
    have h2 : f a ≤ f b := mf hab
    have h3 : g a ≤ g b := mg hab
    calc (f + g) a
         = f a + g a := rfl
       _ ≤ f b + g b := add_le_add h2 h3
       _ = (f + g) b := rfl }
  show Monotone (f + g)
  exact h1

-- 2ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b := by
  { intros a b hab
    calc (f + g) a
         = f a + g a := rfl
       _ ≤ f b + g b := add_le_add (mf hab) (mg hab)
       _ = (f + g) b := rfl }
  show Monotone (f + g)
  exact h1

-- 3ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g) b := by
  { intros a b hab
    show (f + g) a ≤ (f + g) b
    exact add_le_add (mf hab) (mg hab) }
  show Monotone (f + g)
  exact h1

-- 4ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
by
  -- a b : ℝ
  -- hab : a ≤ b
  intros a b hab
  apply add_le_add
  . -- f a ≤ f b
    apply mf hab
  . --  g a ≤ g b
    apply mg hab

-- 5ª demostración
example
  (mf : Monotone f)
  (mg : Monotone g)
  : Monotone (f + g) :=
λ _ _ hab ↦ add_le_add (mf hab) (mg hab)

-- Lemas usados
-- ============

-- variable (a b c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
