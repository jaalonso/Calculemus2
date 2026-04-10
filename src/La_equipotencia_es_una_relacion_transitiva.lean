-- La_equipotencia_es_una_relacion_transitiva.lean
-- La equipotencia es una relación transitiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-junio-2024
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
-- Demostrar que la relación de equipotencia es transitiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean X, Y, Z tales que X ⋍ Y y Y ⋍ Z. Entonces, existen f: X → Y y
-- g: Y → Z que son biyectivas. Por tanto, g ∘ f: X → Z es biyectiva y
-- X ⋍ Z.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

def es_equipotente (A B : Type _) :=
  ∃ g : A → B, Bijective g

local infixr:50 " ⋍ " => es_equipotente

-- 1ª demostración
-- ===============

example : IsTrans _ (. ⋍ .) :=
⟨fun X Y Z hXY hYZ => by
   -- X Y Z : Type ?u.8772
   -- hXY : X ⋍ Y
   -- hYZ : Y ⋍ Z
   -- ⊢ X ⋍ Z
   unfold es_equipotente at *
   -- hXY : ∃ g, Bijective g
   -- hYZ : ∃ g, Bijective g
   -- ⊢ ∃ g, Bijective g
   cases' hXY with f hf
   -- f : X → Y
   -- hf : Bijective f
   cases' hYZ with g hg
   -- g : Y → Z
   -- hg : Bijective g
   use (g ∘ f)
   -- ⊢ Bijective (g ∘ f)
   exact Bijective.comp hg hf⟩

-- 2ª demostración
-- ===============

example : IsTrans _ (. ⋍ .) :=
⟨fun _ _ _ ⟨f, hf⟩ ⟨g, hg⟩ =>
  ⟨g ∘ f, Bijective.comp hg hf⟩⟩

-- 3ª demostración
-- ===============

example : IsTrans _ (. ⋍ .) :=
⟨fun _ _ _ ⟨f, hf⟩ ⟨g, hg⟩ ↦ ⟨g ∘ f, Bijective.comp hg hf⟩⟩

-- Lemas usados
-- ============

-- variable {X Y Z : Type}
-- variable {f : X → Y}
-- variable {g : Y → Z}
-- #check (Bijective.comp : Bijective g → Bijective f → Bijective (g ∘ f))
