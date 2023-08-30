-- Conmutatividad_del_minimo.lean
-- En ℝ, min(a,b) = min(b,a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a y b números reales. Demostrar que
--    min a b = min b a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia de la siguiente propiedad
--    min(a, b) ≤ min(b, a)                                          (1)
-- En efecto, intercambiando las variables en (1) se obtiene
--    min(b, a) ≤ min(a, b)                                          (2)
-- Finalmente de (1) y (2) se obtiene
--    min(b, a) = min(a, b)
--
-- Para demostrar (1), se observa que
--    min(a, b) ≤ b
--    min(a, b) ≤ a
-- y, por tanto,
--    min(a, b) = min(b, a)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- Lema auxiliar
-- =============

-- 1ª demostración del lema auxiliar
-- =================================

example : min a b ≤ min b a :=
by
  have h1 : min a b ≤ b := min_le_right a b
  have h2 : min a b ≤ a := min_le_left a b
  show min a b ≤ min b a
  exact le_min h1 h2

-- 2ª demostración del lema auxiliar
-- =================================

example : min a b ≤ min b a :=
by
  apply le_min
  { apply min_le_right }
  { apply min_le_left }

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux : min a b ≤ min b a :=
by exact le_min (min_le_right a b) (min_le_left a b)

-- 1ª demostración
-- ===============

example : min a b = min b a :=
by
  apply le_antisymm
  { exact aux a b}
  { exact aux b a}

-- 2ª demostración
-- ===============

example : min a b = min b a :=
le_antisymm (aux a b) (aux b a)

-- 3ª demostración
-- ===============

example : min a b = min b a :=
min_comm a b

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- #check (min_comm a b : min a b = min b a)
-- #check (min_le_left a b : min a b ≤ a)
-- #check (min_le_right a b : min a b ≤ b)
