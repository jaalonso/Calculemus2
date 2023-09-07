-- Propiedad_distributiva_1.lean
-- En los retículos, una distributiva del ínfimo implica la otra.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si α es un retículo tal que
--    ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
-- entonces
--    (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
-- para todos los elementos de α.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra por la siguiente cadena de igualdades
--    (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)          [por conmutatividad de ⊓]
--                = (c ⊓ a) ⊔ (c ⊓ b)    [por la hipótesis]
--                = (a ⊓ c) ⊔ (c ⊓ b)    [por conmutatividad de ⊓]
--                = (a ⊓ c) ⊔ (b ⊓ c)    [por conmutatividad de ⊓]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (a b c : α)

-- 1ª demostración
example
  (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
calc
  (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)       := by rw [inf_comm]
            _ = (c ⊓ a) ⊔ (c ⊓ b) := by rw [h]
            _ = (a ⊓ c) ⊔ (c ⊓ b) := by rw [@inf_comm _ _ c a]
            _ = (a ⊓ c) ⊔ (b ⊓ c) := by rw [@inf_comm _ _ c b]

-- 2ª demostración
example
  (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
by simp [h, inf_comm]

-- Lemas usados
-- ============

-- #check (inf_comm : a ⊓ b = b ⊓ a)
