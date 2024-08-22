-- Suma_nula_de_dos_cuadrados.lean
-- En ℝ, x² + y² = 0 ↔ x = 0 ∧ y = 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-diciembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si x, y ∈ ℝ, entonces
--    x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos el siguiente lema auxiliar
--    (∀ x, y ∈ ℝ)[x² + y² = 0 → x = 0]
--
-- Para la primera implicación, supongamos que
--    x² + y² = 0                                                    (1)
-- Entonces, por el lema auxiliar,
--    x = 0                                                          (2)
-- Además, aplicando la conmutativa a (1), se tiene
--    y² + x² = 0
-- y, por el lema auxiliar,
--    y = 0                                                          (3)
-- De (2) y (3) se tiene
--    x = 0 ∧ y = 0
--
-- Para la segunda implicación, supongamos que
--    x = 0 ∧ y = 0
-- Por tanto,
--    x² + y² = 0² + 0²
--            = 0
--
-- En la demostración del lema auxiliar se usarán los siguientes lemas
--    (∀ x ∈ ℝ)(∀ n ∈ ℕ)[x^n = 0 → x = 0]                            (L1)
--    (∀ x, y ∈ ℝ)[x ≤ y → y ≤ x → x = y]                            (L2)
--    (∀ x, y ∈ ℝ)[0 ≤ y → x ≤ x + y]                                (L3)
--    (∀ x ∈ ℝ)[0 ≤ x²]                                              (L4)
--
-- Por el lema L1, para demostrar el lema auxiliar basta demostrar
--    x² = 0                                                         (1)
-- y, por el lema L2, basta demostrar las siguientes desigualdades
--     x² ≤ 0                                                        (2)
--     0 ≤ x²                                                        (3)
--
-- La prueba de la (2) es
--    x² ≤ x² + y²   [por L3 y L4]
--       = 0         [por la hipótesis]
--
-- La (3) se tiene por el lema L4.

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {x y : ℝ}

-- 1ª demostración del lema auxiliar
-- =================================

example
  (h : x^2 + y^2 = 0)
  : x = 0 :=
by
  have h' : x^2 = 0 := by
  { apply le_antisymm
    . show x ^ 2 ≤ 0
      calc x ^ 2 ≤ x^2 + y^2 := by simp [le_add_of_nonneg_right,
                                         pow_two_nonneg]
               _ = 0         := by exact h
    . show 0 ≤ x ^ 2
      apply pow_two_nonneg }
  show x = 0
  exact pow_eq_zero h'

-- 2ª demostración lema auxiliar
-- =============================

example
  (h : x^2 + y^2 = 0)
  : x = 0 :=
by
  have h' : x^2 = 0 := by
  { apply le_antisymm
    . -- ⊢ x ^ 2 ≤ 0
      calc x ^ 2 ≤ x^2 + y^2 := by simp [le_add_of_nonneg_right,
                                         pow_two_nonneg]
               _ = 0         := by exact h
    . -- ⊢ 0 ≤ x ^ 2
      apply pow_two_nonneg }
  exact pow_eq_zero h'

-- 3ª demostración lema auxiliar
-- =============================

lemma aux
  (h : x^2 + y^2 = 0)
  : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

-- 1ª demostración
-- ===============

example : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
by
  constructor
  . -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    . -- ⊢ x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : x ^ 2 + y ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    intro h1
    -- h1 : x = 0 ∧ y = 0
    -- ⊢ x ^ 2 + y ^ 2 = 0
    rcases h1 with ⟨h2, h3⟩
    -- h2 : x = 0
    -- h3 : y = 0
    rw [h2, h3]
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- 2ª demostración
-- ===============

example : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
by
  constructor
  . -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    . -- ⊢ x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : x ^ 2 + y ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    rintro ⟨h1, h2⟩
    -- h1 : x = 0
    -- h2 : y = 0
    -- ⊢ x ^ 2 + y ^ 2 = 0
    rw [h1, h2]
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- 3ª demostración
-- ===============

example : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · -- ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    -- h : x ^ 2 + y ^ 2 = 0
    -- ⊢ x = 0 ∧ y = 0
    constructor
    · -- x = 0
      exact aux h
    . -- ⊢ y = 0
      rw [add_comm] at h
      -- h : y ^ 2 + x ^ 2 = 0
      exact aux h
  . -- ⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    rintro ⟨rfl, rfl⟩
    -- ⊢ 0 ^ 2 + 0 ^ 2 = 0
    norm_num

-- Lemas usados
-- ============

-- #check (add_comm x y : x + y = y + x)
-- #check (le_add_of_nonneg_right : 0 ≤ y → x ≤ x + y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (pow_eq_zero : ∀ {n : ℕ}, x ^ n = 0 → x = 0)
-- #check (pow_two_nonneg x : 0 ≤ x ^ 2)
