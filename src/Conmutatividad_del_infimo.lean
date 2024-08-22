-- Conmutatividad_del_infimo.lean
-- En los retículos, x ⊓ y = y ⊓ x
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los retículos se verifica que
--     x ⊓ y = y ⊓ x
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia del siguiente lema auxiliar
--    (∀ a, b)[a ⊓ b ≤ b ⊓ a]                                         (1)
-- En efecto, sustituyendo en (1) a por x y b por y, se tiene
--    x ⊓ y ≤ y ⊓ x                                                   (2)
-- y sustituyendo en (1) a por y y b por x, se tiene
--    y ⊓ x ≤ x ⊓ y                                                   (3)
-- Finalmente, aplicando la propiedad antisimétrica de la divisibilidad
-- a (2) y (3), se tiene
--    x ⊓ y = y ⊓ x
--
-- Para demostrar (1), por la definición del ínfimo, basta demostrar
-- las siguientes relaciones
--    y ⊓ x ≤ x
--    y ⊓ x ≤ y
-- y ambas se tienen por la definición del ínfimo.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Order.Lattice
variable {α : Type _} [Lattice α]
variable (x y z : α)

-- 1ª demostración del lema auxiliar
lemma aux : x ⊓ y ≤ y ⊓ x :=
by
  have h1 : x ⊓ y ≤ y :=
    inf_le_right
  have h2 : x ⊓ y ≤ x :=
    inf_le_left
  show x ⊓ y ≤ y ⊓ x
  exact le_inf h1 h2

-- 2ª demostración del lema auxiliar
example : x ⊓ y ≤ y ⊓ x :=
by
  apply le_inf
  { apply inf_le_right }
  { apply inf_le_left }

-- 3ª demostración del lema auxiliar
example : x ⊓ y ≤ y ⊓ x :=
le_inf inf_le_right inf_le_left

-- 1ª demostración
example : x ⊓ y = y ⊓ x :=
by
  have h1 : x ⊓ y ≤ y ⊓ x :=
    aux x y
  have h2 : y ⊓ x ≤ x ⊓ y :=
    aux y x
  show x ⊓ y = y ⊓ x
  exact le_antisymm h1 h2

-- 2ª demostración
example : x ⊓ y = y ⊓ x :=
by
  apply le_antisymm
  { apply aux }
  { apply aux }

-- 3ª demostración
example : x ⊓ y = y ⊓ x :=
le_antisymm (aux x y) (aux y x)

-- 4ª demostración
example : x ⊓ y = y ⊓ x :=
by apply le_antisymm; simp ; simp

-- 5ª demostración
example : x ⊓ y = y ⊓ x :=
-- by exact?
inf_comm x y

-- Lemas usados
-- ============

-- #check (inf_comm x y : x ⊓ y = y ⊓ x)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
