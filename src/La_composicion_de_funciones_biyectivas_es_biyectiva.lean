-- La_composicion_de_funciones_biyectivas_es_biyectiva.lean
-- La composición de funciones biyectivas es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de dos funciones biyectivas es una
-- función biyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean f: X → Y y g: Y → Z. En ejercicios anteriores hemos demostrados
-- los siguientes lemas:
-- + Lema 1: Si f y g son inyectiva, entonces también lo es g ∘ f.
-- + Lema 2: Si f y g son suprayectiva, entonces también lo es g ∘ f.
--
-- Supongamos que f y g son biyectivas. Entonces, son inyectivas y
-- suprayectivas. Luego, por los lemas 1 y 2, g ∘ f es inyectiva y
-- suprayectiva. Por tanto, g ∘ f es biyectiva.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

variable {X Y Z : Type}
variable {f : X → Y}
variable {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  constructor
  . -- ⊢ Injective (g ∘ f)
    apply Injective.comp
    . -- ⊢ Injective g
      exact Hgi
    . -- ⊢ Injective f
      exact Hfi
  . apply Surjective.comp
    . -- ⊢ Surjective g
      exact Hgs
    . -- ⊢ Surjective f
      exact Hfs

-- 2ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  constructor
  . -- ⊢ Injective (g ∘ f)
    exact Injective.comp Hgi Hfi
  . -- ⊢ Surjective (g ∘ f)
    exact Surjective.comp Hgs Hfs

-- 3ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
by
  cases' Hf with Hfi Hfs
  -- Hfi : Injective f
  -- Hfs : Surjective f
  cases' Hg with Hgi Hgs
  -- Hgi : Injective g
  -- Hgs : Surjective g
  exact ⟨Injective.comp Hgi Hfi,
         Surjective.comp Hgs Hfs⟩

-- 4ª demostración
-- ===============

example :
  Bijective f → Bijective g → Bijective (g ∘ f) :=
by
  rintro ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩
  -- Hfi : Injective f
  -- Hfs : Surjective f
  -- Hgi : Injective g
  -- Hgs : Surjective g
  exact ⟨Injective.comp Hgi Hfi,
         Surjective.comp Hgs Hfs⟩

-- 5ª demostración
-- ===============

example :
  Bijective f → Bijective g → Bijective (g ∘ f) :=
fun ⟨Hfi, Hfs⟩ ⟨Hgi, Hgs⟩ ↦ ⟨Injective.comp Hgi Hfi,
                             Surjective.comp Hgs Hfs⟩

-- 6ª demostración
-- ===============

example
  (Hf : Bijective f)
  (Hg : Bijective g)
  : Bijective (g ∘ f) :=
Bijective.comp Hg Hf

-- Lemas usados
-- ============

-- #check (Bijective.comp : Bijective g → Bijective f → Bijective (g ∘ f))
-- #check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
-- #check (Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f))
