-- Caracterizacion_de_producto_igual_al_primer_factor.lean
-- Caracterización de producto igual al primer factor
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un monoide cancelativo por la izquierda es un monoide M que cumple la
-- propiedad cancelativa por la izquierda; es decir, para todo a, b ∈ M
--    a * b = a * c ↔ b = c.
--
-- En Lean4 la clase de los monoides cancelativos por la izquierda es
-- LeftCancelMonoid y la propiedad cancelativa por la izquierda es
--    mul_left_cancel : a * b = a * c → b = c
--
-- Demostrar que si M es un monoide cancelativo por la izquierda y
-- a, b ∈ M, entonces
--    a * b = a ↔ b = 1
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Demostraremos las dos implicaciones.
--
-- (⟹) Supongamos que
--    a·b = a                                                        (1)
-- Por la propiedad del neutro por la derecha tenemos
--    a·1 = a                                                        (2)
-- Por tanto,
--    a·b = a·1
-- y, por la propiedad cancelativa,
--    b = 1
--
-- (⟸) Supongamos que b = 1. Entonces,
--    a·b = a·1
--        = a      [por el neutro por la derecha]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {M : Type} [LeftCancelMonoid M]
variable {a b : M}

-- 1ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by
  constructor
  . -- ⊢ a * b = a → b = 1
    intro h
    -- h : a * b = a
    -- ⊢ b = 1
    have h1 : a * b = a * 1 := by
      calc a * b = a     := by exact h
               _ = a * 1 := (mul_one a).symm
    exact mul_left_cancel h1
  . -- ⊢ b = 1 → a * b = a
    intro h
    -- h : b = 1
    -- ⊢ a * b = a
    rw [h]
    -- ⊢ a * 1 = a
    exact mul_one a

-- 2ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
calc a * b = a
     ↔ a * b = a * 1 := by rw [mul_one]
   _ ↔ b = 1         := mul_left_cancel_iff

-- 3ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
mul_right_eq_self

-- 4ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by aesop

-- Lemas usados
-- ============

-- variable (c : M)
-- #check (mul_left_cancel : a * b = a * c → b = c)
-- #check (mul_one a : a * 1 = a)
-- #check (mul_right_eq_self : a * b = a ↔ b = 1)
