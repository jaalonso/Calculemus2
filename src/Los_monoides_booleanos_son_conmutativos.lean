-- Los_monoides_booleanos_son_conmutativos.lean
-- Los monoides booleanos son conmutativos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un monoide es un conjunto junto con una operación binaria que es
-- asociativa y tiene elemento neutro.
--
-- Un monoide M es booleano si
--    ∀ x ∈ M, x * x = 1
-- y es conmutativo si
--    ∀ x y ∈ M, x * y = y * x
--
-- En Lean4, está definida la clase de los monoides (como `Monoid`) y sus
-- propiedades características son
--    mul_assoc : (a * b) * c = a * (b * c)
--    one_mul :   1 * a = a
--    mul_one :   a * 1 = a
--
-- Demostrar que los monoides booleanos son conmutativos.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean a, b ∈ M. Se verifica la siguiente cadena de igualdades
--    a·b = (a·b)·1               [por mul_one]
--        = (a·b)·(a·a)           [por hipótesis, a·a = 1]
--        = ((a·b)·a)·a           [por mul_assoc]
--        = (a·(b·a))·a           [por mul_assoc]
--        = (1·(a·(b·a)))·a       [por one_mul]
--        = ((b·b)·(a·(b·a)))·a   [por hipótesis, b·b = 1]
--        = (b·(b·(a·(b·a))))·a   [por mul_assoc]
--        = (b·((b·a)·(b·a)))·a   [por mul_assoc]
--        = (b·1)·a               [por hipótesis, (b·a)·(b·a) = 1]
--        = b·a                   [por mul_one]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Basic

variable {M : Type} [Monoid M]

-- 1ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1
         := (mul_one (a * b)).symm
     _ = (a * b) * (a * a)
         := congrArg ((a*b) * .) (h a).symm
     _ = ((a * b) * a) * a
         := (mul_assoc (a*b) a a).symm
     _ = (a * (b * a)) * a
         := congrArg (. * a) (mul_assoc a b a)
     _ = (1 * (a * (b * a))) * a
         := congrArg (. * a) (one_mul (a*(b*a))).symm
     _ = ((b * b) * (a * (b * a))) * a
         := congrArg (. * a) (congrArg (. * (a*(b*a))) (h b).symm)
     _ = (b * (b * (a * (b * a)))) * a
         := congrArg (. * a) (mul_assoc b b (a*(b*a)))
     _ = (b * ((b * a) * (b * a))) * a
         := congrArg (. * a) (congrArg (b * .) (mul_assoc b a (b*a)).symm)
     _ = (b * 1) * a
         := congrArg (. * a) (congrArg (b * .) (h (b*a)))
     _ = b * a
         := congrArg (. * a) (mul_one b)

-- 2ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp only [mul_one]
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = ((a * b) * a) * a             := by simp only [mul_assoc]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp only [one_mul]
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * (b * (a * (b * a)))) * a := by simp only [mul_assoc]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp only [mul_one]
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp only [one_mul]
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp only [mul_one]

-- 4ª demostración
-- ===============

example
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
by
  intros a b
  calc a * b
       = (a * b) * 1                   := by simp
     _ = (a * b) * (a * a)             := by simp only [h a]
     _ = (a * (b * a)) * a             := by simp only [mul_assoc]
     _ = (1 * (a * (b * a))) * a       := by simp
     _ = ((b * b) * (a * (b * a))) * a := by simp only [h b]
     _ = (b * ((b * a) * (b * a))) * a := by simp only [mul_assoc]
     _ = (b * 1) * a                   := by simp only [h (b*a)]
     _ = b * a                         := by simp

-- Lemas usados
-- ============

-- variable (a b c : M)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
