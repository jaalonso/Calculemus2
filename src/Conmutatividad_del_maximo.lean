-- Conmutatividad_del_maximo.lean
-- En ℝ, max(a,b) = max(b,a)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a y b números reales. Demostrar que
--    max a b = max b a
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia de la siguiente propiedad
--    max(a, b) ≤ max(b, a)                                          (1)
-- En efecto, intercambiando las variables en (1) se obtiene
--    max(b, a) ≤ max(a, b)                                          (2)
-- Finalmente de (1) y (2) se obtiene
--    max(b, a) = max(a, b)
--
-- Para demostrar (1), se observa que
--    a ≤ max(b, a)
--    b ≤ max(b, a)
-- y, por tanto,
--    max(a, b) ≤ max(b, a)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (a b : ℝ)

-- Lema auxiliar
-- =============

-- 1ª demostración del lema auxiliar
-- =================================

example : max a b ≤ max b a :=
by
  have h1 : a ≤ max b a := le_max_right b a
  have h2 : b ≤ max b a := le_max_left b a
  show max a b ≤ max b a
  exact max_le h1 h2

-- 2ª demostración del lema auxiliar
-- =================================

example : max a b ≤ max b a :=
by
  apply max_le
  { apply le_max_right }
  { apply le_max_left }

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux : max a b ≤ max b a :=
by exact max_le (le_max_right b a) (le_max_left b a)

-- 1ª demostración
-- ===============

example : max a b = max b a :=
by
  apply le_antisymm
  { exact aux a b}
  { exact aux b a}

-- 2ª demostración
-- ===============

example : max a b = max b a :=
le_antisymm (aux a b) (aux b a)

-- 3ª demostración
-- ===============

example : max a b = max b a :=
max_comm a b

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (max_comm a b : max a b = max b a)
-- #check (max_le : a ≤ c → b ≤ c → max a b ≤ c)
