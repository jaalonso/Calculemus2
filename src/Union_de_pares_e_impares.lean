-- Union_de_pares_e_impares.lean
-- Pares ∪ Impares = Naturales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Los conjuntos de los números naturales, de los pares y de los impares
-- se definen por
--    def Naturales : Set ℕ := {n | True}
--    def Pares     : Set ℕ := {n | Even n}
--    def Impares   : Set ℕ := {n | ¬Even n}
--
-- Demostrar que
--    Pares ∪ Impares = Naturales
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    {n | Even n} ∪ {n | ¬Even n} = {n | True}
-- es decir,
--    n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
-- que se reduce a
--    ⊢ Even n ∨ ¬Even n
-- que es una tautología.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Parity

def Naturales : Set ℕ := {_n | True}
def Pares     : Set ℕ := {n | Even n}
def Impares   : Set ℕ := {n | ¬Even n}

-- 1ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  simp only [Set.mem_setOf_eq, iff_true]
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n}
  exact em (Even n)

-- 2ª demostración
-- ===============

example : Pares ∪ Impares = Naturales :=
by
  unfold Pares Impares Naturales
  -- ⊢ {n | Even n} ∪ {n | ¬Even n} = {n | True}
  ext n
  -- ⊢ n ∈ {n | Even n} ∪ {n | ¬Even n} ↔ n ∈ {n | True}
  tauto
