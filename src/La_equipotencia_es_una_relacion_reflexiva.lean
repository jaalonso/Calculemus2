-- La_equipotencia_es_una_relacion_reflexiva.lean
-- La equipotencia es una relación reflexiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 18-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Dos conjuntos A y B son equipotentes (y se denota por A ≃ B) si
-- existe una aplicación biyectiva entre ellos. La equipotencia se puede
-- definir en Lean por
--    def es_equipotente (A B : Type _) : Prop :=
--      ∃ g : A → B, Bijective g
--
--    local infixr:50 " ⋍ " => es_equipotente
--
-- Demostrar que la relación de equipotencia es reflexiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostra que para cualquier X, se tiene que X es
-- equipotente a X. Para demostrarlo basta considerar que la función
-- identidad en X es una biyección de X en X.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Function

def es_equipotente (A B : Type _) : Prop :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

-- 1ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
by
  intro X
  -- ⊢ X ⋍ X
  use id
  -- ⊢ Bijective id
  exact bijective_id

-- 2ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
by
  intro X
  -- ⊢ X ⋍ X
  exact ⟨id, bijective_id⟩

-- 3ª demostración
-- ===============

example : Reflexive (. ⋍ .) :=
fun _ ↦ ⟨id, bijective_id⟩

-- Lemas usados
-- ============

-- #check (bijective_id : Bijective id)
