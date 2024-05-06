-- Equivalencia_de_inversos_iguales_al_neutro.lean
-- Equivalencia de inversos iguales al neutro
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea M un monoide y a, b ∈ M tales que a * b = 1. Demostrar que a = 1
-- si y sólo si b = 1.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Demostraremos las dos implicaciones.
--
-- (⟹) Supongamos que a = 1. Entonces,
--    b = 1·b    [por neutro por la izquierda]
--      = a·b    [por supuesto]
--      = 1      [por hipótesis]
--
-- (⟸) Supongamos que b = 1. Entonces,
--    a = a·1    [por neutro por la derecha]
--      = a·b    [por supuesto]
--      = 1      [por hipótesis]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]
variable {a b : M}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    intro a1
    -- a1 : a = 1
    -- ⊢ b = 1
    calc b = 1 * b := (one_mul b).symm
         _ = a * b := congrArg (. * b) a1.symm
         _ = 1     := h
  . -- ⊢ b = 1 → a = 1
    intro b1
    -- b1 : b = 1
    -- ⊢ a = 1
    calc a = a * 1 := (mul_one a).symm
         _ = a * b := congrArg (a * .) b1.symm
         _ = 1     := h

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    intro a1
    -- a1 : a = 1
    -- ⊢ b = 1
    rw [a1] at h
    -- h : 1 * b = 1
    rw [one_mul] at h
    -- h : b = 1
    exact h
  . -- ⊢ b = 1 → a = 1
    intro b1
    -- b1 : b = 1
    -- ⊢ a = 1
    rw [b1] at h
    -- h : a * 1 = 1
    rw [mul_one] at h
    -- h : a = 1
    exact h

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by
  constructor
  . -- ⊢ a = 1 → b = 1
    rintro rfl
    -- h : 1 * b = 1
    simpa using h
  . -- ⊢ b = 1 → a = 1
    rintro rfl
    -- h : a * 1 = 1
    simpa using h

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by constructor <;> (rintro rfl; simpa using h)

-- 5ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
eq_one_iff_eq_one_of_mul_eq_one h

-- Lemas usados
-- ============

-- #check (eq_one_iff_eq_one_of_mul_eq_one : a * b = 1 → (a = 1 ↔ b = 1))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
