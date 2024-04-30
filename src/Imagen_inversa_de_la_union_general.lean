-- Imagen_inversa_de_la_union_general.lean
-- Imagen inversa de la unión general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f⁻¹[⋃ᵢ Bᵢ] = ⋃ᵢ f⁻¹[Bᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que, para todo x,
--    x ∈ f⁻¹[⋃ᵢ Bᵢ] ↔ x ∈ ⋃ᵢ f⁻¹[Bᵢ]
-- y lo haremos demostrando las dos implicaciones.
--
-- (⟹) Supongamos que x ∈ f⁻¹[⋃ᵢ Bᵢ]. Entonces, por la definición de la
-- imagen inversa,
--    f(x) ∈ ⋃ᵢ Bᵢ
-- y, por la definición de la unión, existe un i tal que
--    f(x) ∈ Bᵢ
-- y, por la definición de la imagen inversa,
--    x ∈ f⁻¹[Bᵢ]
-- y, por la definición de la unión,
--    x ∈ ⋃ᵢ f⁻¹[Bᵢ]
--
-- (⟸) Supongamos que x ∈ ⋃ᵢ f⁻¹[Bᵢ]. Entonces, por la definición de la
-- unión, existe un i tal que
--    x ∈ f⁻¹[Bᵢ]
-- y, por la definición de la imagen inversa,
--    f(x) ∈ Bᵢ
-- y, por la definición de la unión,
--    f(x) ∈ ⋃ᵢ Bᵢ
-- y, por la definición de la imagen inversa,
--    x ∈ f⁻¹[⋃ᵢ Bᵢ]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

variable {α β I : Type _}
variable (f : α → β)
variable (B : I → Set β)

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i ↔ x ∈ ⋃ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i → x ∈ ⋃ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋃ (i : I), B i
    -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, f x ∈ B i
    cases' hx with i fxBi
    -- i : I
    -- fxBi : f x ∈ B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, x ∈ f ⁻¹' B i
    use i
    -- ⊢ x ∈ f ⁻¹' B i
    apply mem_preimage.mpr
    -- ⊢ f x ∈ B i
    exact fxBi
  . -- ⊢ x ∈ ⋃ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋃ (i : I), B i
    intro hx
    -- hx : x ∈ ⋃ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋃ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋃ (i : I), B i
    rw [mem_iUnion]
    -- ⊢ ∃ i, f x ∈ B i
    rw [mem_iUnion] at hx
    -- hx : ∃ i, x ∈ f ⁻¹' B i
    cases' hx with i xBi
    -- i : I
    -- xBi : x ∈ f ⁻¹' B i
    use i
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at xBi
    -- xBi : f x ∈ B i
    exact xBi

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_iUnion

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by  simp

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set β)
-- variable (A : I → Set α)
-- #check (mem_iUnion : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i)
-- #check (mem_preimage : x ∈ f ⁻¹' s ↔ f x ∈ s)
-- #check (preimage_iUnion : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i))
