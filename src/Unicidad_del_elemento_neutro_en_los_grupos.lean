-- Unicidad_del_elemento_neutro_en_los_grupos.lean
-- Unicidad del elemento neutro en los grupos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que un grupo sólo posee un elemento neutro.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea e ∈ G tal que
--    (∀ x)[x·e = x]                                                 (1)
-- Entonces,
--    e = 1.e    [porque 1 es neutro]
--      = 1      [por (1)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {G : Type} [Group G]

-- 1ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
calc e = 1 * e := (one_mul e).symm
     _ = 1     := h 1

-- 2ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by
  have h1 : e = e * e := (h e).symm
  exact self_eq_mul_left.mp h1

-- 3ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
self_eq_mul_left.mp (h e).symm

-- 4ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by aesop

-- Lemas usados
-- ============

-- variable (a b : G)
-- #check (one_mul a : 1 * a = a)
-- #check (self_eq_mul_left : b = a * b ↔ a = 1)
