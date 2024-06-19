-- La_inversa_de_una_funcion_biyectiva_es_biyectiva.lean
-- La inversa de una función es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
--
-- Demostrar que si g es una inversa de f, entonces g es biyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrar que g: Y → X es biyectiva, basta probar que existe una
-- h que es inversa de g por la izquierda y por la derecha; es decir,
--    (∀y ∈ Y)[(h ∘ g)(y) = y]                                       (1)
--    (∀x ∈ X)[(g ∘ h)(x) = x]                                       (2)
--
-- Puesto que g es una inversa de f, entonces
--    (∀x ∈ X)[(g ∘ f)(x) = x]                                       (3)
--    (∀y ∈ Y)[(f ∘ g)(y) = y]                                       (4)
--
-- Tomando f como h, (1) se verifica por (4) y (2) se verifica por (3).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)
variable (g : Y → X)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

-- 1ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  constructor
  . -- ⊢ LeftInverse f g
    exact h1
  . -- ⊢ Function.RightInverse f g
    exact h2

-- 2ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  exact ⟨h1, h2⟩

-- 3ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rcases hg with ⟨h1, h2⟩
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, ⟨h1, h2⟩⟩

-- 4ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  use f
  -- ⊢ LeftInverse f g ∧ Function.RightInverse f g
  exact hg

-- 5ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  rw [bijective_iff_has_inverse]
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

-- 6ª demostración
-- ===============

example
  (hg : inversa g f)
  : Bijective g :=
by
  apply bijective_iff_has_inverse.mpr
  -- ⊢ ∃ g_1, LeftInverse g_1 g ∧ Function.RightInverse g_1 g
  exact ⟨f, hg⟩

-- Lemas usados
-- ============

-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
