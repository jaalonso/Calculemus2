-- Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.lean
-- Si f es suprayectiva, entonces u ⊆ f[f⁻¹[u]].
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla,  2-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea y ∈ u. Por ser f suprayectiva, exite un x tal que
--    f(x) = y                                                       (1)
-- Por tanto, x ∈ f⁻¹[u] y
--    f(x) ∈ f[f⁻¹[u]]                                               (2)
-- Finalmente, por (1) y (2),
--    y ∈ f[f⁻¹[u]]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
open Set Function
variable {α β : Type _}
variable (f : α → β)
variable (u : Set β)

-- 1ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  { -- ⊢ x ∈ f ⁻¹' u
    apply mem_preimage.mpr
    -- ⊢ f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu }
  { -- ⊢ f x = y
    exact fxy }

-- 2ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  use x
  -- ⊢ x ∈ f ⁻¹' u ∧ f x = y
  constructor
  { show f x ∈ u
    rw [fxy]
    -- ⊢ y ∈ u
    exact yu }
  { show f x = y
    exact fxy }

-- 3ª demostración
-- ===============

example
  (h : Surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
by
  intros y yu
  -- y : β
  -- yu : y ∈ u
  -- ⊢ y ∈ f '' (f ⁻¹' u)
  rcases h y with ⟨x, fxy⟩
  -- x : α
  -- fxy : f x = y
  aesop

-- Lemas usados
-- ============

-- variable (x : α)
-- #check (mem_preimage : x ∈ f ⁻¹' u ↔ f x ∈ u)
