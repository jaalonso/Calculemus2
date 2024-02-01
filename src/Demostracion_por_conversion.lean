-- Demostracion_por_conversion.lean
-- En ℝ, si 1 < a, entonces a < aa
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-febrero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar, para todo a ∈ ℝ, si
--    1 < a
-- entonces
--    a < a * a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se usarán los siguientes lemas
--    L1: 0 < 1
--    L2: (∀ a ∈ ℝ[1a = a]
--    L3: (∀ a, b, c ∈ ℝ)[0 < a → (ba < ca ↔ b < c)]
--
-- En primer lugar, tenemos que
--    0 < a                                                          (1)
-- ya que
--    0 < 1    [por L1]
--      < a    [por la hipótesis]
-- Entonces,
--    a = 1a   [por L2]
--      < aa   [por L3, (1) y la hipótesis]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
variable {a : ℝ}

-- 1ª demostración
-- ===============

example
  (h : 1 < a)
  : a < a * a :=
by
  have h1 : 0 < a := calc
    0 < 1 := zero_lt_one
    _ < a := h
  show a < a * a
  calc a = 1 * a := (one_mul a).symm
       _ < a * a := (mul_lt_mul_right h1).mpr h

-- Comentarios: La táctica (convert e) genera nuevos subojetivos cuya
-- conclusiones son las diferencias entre el tipo de e y la conclusión.

-- 2ª demostración
-- ===============

example
  (h : 1 < a)
  : a < a * a :=
by
  convert (mul_lt_mul_right _).2 h
  . -- ⊢ a = 1 * a
    rw [one_mul]
  . -- ⊢ 0 < a
    exact lt_trans zero_lt_one h

-- Lemas usados
-- ============

-- variables (a b c : ℝ)
-- #check (mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c))
-- #check (one_mul a : 1 * a = a)
-- #check (lt_trans : a < b → b < c → a < c)
-- #check (zero_lt_one : 0 < 1)
