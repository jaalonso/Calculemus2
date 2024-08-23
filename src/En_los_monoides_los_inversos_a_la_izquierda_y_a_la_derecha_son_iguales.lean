-- En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.lean
-- En los monoides, los inversos a la izquierda y a la derecha son iguales.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  3-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto
-- junto con una operación binaria que es asociativa y tiene elemento
-- neutro.
--
-- En Lean, está definida la clase de los monoides (como `monoid`) y sus
-- propiedades características son
--    mul_assoc : (a * b) * c = a * (b * c)
--    one_mul :   1 * a = a
--    mul_one :   a * 1 = a
--
-- Demostrar que si M es un monoide, a ∈ M, b es un inverso de a por la
-- izquierda y c es un inverso de a por la derecha, entonces b = c.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la siguiente cadena de igualdades
--    b = b * 1          [por mul_one]
--      = b * (a * c)    [por hipótesis]
--      = (b * a) * c    [por mul_assoc]
--      = 1 * c          [por hipótesis]
--      = c              [por one_mul]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

variable {M : Type} [Monoid M]
variable {a b c : M}

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b = b * 1       := (mul_one b).symm
     _ = b * (a * c) := congrArg (b * .) hac.symm
     _ = (b * a) * c := (mul_assoc b a c).symm
     _ = 1 * c       := congrArg (. * c) hba
     _ = c           := one_mul c

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b  = b * 1       := by aesop
      _ = b * (a * c) := by aesop
      _ = (b * a) * c := (mul_assoc b a c).symm
      _ = 1 * c       := by aesop
      _ = c           := by aesop

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by
  rw [←one_mul c]
  -- ⊢ b = 1 * c
  rw [←hba]
  -- ⊢ b = (b * a) * c
  rw [mul_assoc]
  -- ⊢ b = b * (a * c)
  rw [hac]
  -- ⊢ b = b * 1
  rw [mul_one b]

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

-- 5ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
left_inv_eq_right_inv hba hac

-- Lemas usados
-- ============

-- #check (left_inv_eq_right_inv : b * a = 1 → a * c = 1 → b = c)
-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (mul_one a : a * 1 = a)
-- #check (one_mul a : 1 * a = a)
