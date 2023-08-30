-- Inecuaciones_con_exponenciales_2.lean
-- En ℝ, si a ≤ b y c < d, entonces a + eᶜ + f ≤ b + eᵈ + f.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-agosto-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c, d y f son números reales tales que
--    a ≤ b
--    c < d
-- entonces
--    a + eᶜ + f ≤ b + eᵈ + f
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Aplicando a la hipótesis 3 (c < d) la monotonía de la exponencial, se
-- tiene
--    e^c < e^d
-- que, junto a la hipótesis 1 (a ≤ b) y la monotonía de la suma da
--    a + e^c < b + e^d
-- y, de nuevo por la monotonía de la suma, se tiene
--    a + e^c + f < b + e^d + f

-- 2ª demostración en LN
-- =====================

-- Tenemos que demostrar que
--    (a + e^c) + f < (b + e^d) + f
-- que, por la monotonía de la suma, se reduce a las siguientes dos
-- desigualdades:
--    a + e^c < b + e^d                                               (1)
--    f ≤ f                                                           (2)
--
-- La (1), de nuevo por la monotonía de la suma, se reduce a las
-- siguientes dos:
--    a ≤ b                                                         (1.1)
--    e^c < e^d                                                     (1.2)
--
-- La (1.1) se tiene por la hipótesis 1.
--
-- La (1.2) se tiene aplicando la monotonía de la exponencial a la
-- hipótesis 2.
--
-- La (2) se tiene por la propiedad reflexiva.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
variable (a b c d f : ℝ)

-- 1ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  have h3 : exp c < exp d :=
    exp_lt_exp.mpr h2
  have h4 : a + exp c < b + exp d :=
    add_lt_add_of_le_of_lt h1 h3
  show a + exp c + f < b + exp d + f
  exact add_lt_add_right h4 f

-- 2ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  apply add_lt_add_of_lt_of_le
  { apply add_lt_add_of_le_of_lt
    { exact h1 }
    { apply exp_lt_exp.mpr
      exact h2 } }
  { apply le_refl }

-- 3ª demostración
example
  (h1 : a ≤ b)
  (h2 : c < d)
  : a + exp c + f < b + exp d + f :=
by
  apply add_lt_add_of_lt_of_le
  . apply add_lt_add_of_le_of_lt h1
    apply exp_lt_exp.mpr h2
  rfl

-- Lemas usados
-- ============

-- #check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
-- #check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
-- #check (add_lt_add_right : b < c → ∀ (a : ℝ), b + a < c + a)
-- #check (exp_lt_exp : exp a < exp b ↔ a < b)
-- #check (le_refl a : a ≤ a)
