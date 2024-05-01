-- Imagen_inversa_de_la_interseccion_general.lean
-- Imagen inversa de la intersección general
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f⁻¹[⋂ᵢ Bᵢ] = ⋂ᵢ f⁻¹[Bᵢ]
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se demuestra mediante la siguiente cadena de equivalencias
--    x ∈ f⁻¹[⋂ᵢ Bᵢ] ↔ f x ∈ ⋂ᵢ Bᵢ
--                   ↔ (∀ i) f(x) ∈ Bᵢ
--                   ↔ (∀ i) x ∈ f⁻¹[Bᵢ]
--                   ↔ x ∈ ⋂ᵢ f⁻¹[Bᵢ]

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

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  calc  (x ∈ f ⁻¹' ⋂ i, B i)
     ↔ f x ∈ ⋂ i, B i       := mem_preimage
   _ ↔ (∀ i, f x ∈ B i)     := mem_iInter
   _ ↔ (∀ i, x ∈ f ⁻¹' B i) := iff_of_eq rfl
   _ ↔ x ∈ ⋂ i, f ⁻¹' B i   := mem_iInter.symm

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- x : α
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  constructor
  . -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i → x ∈ ⋂ (i : I), f ⁻¹' B i
    intro hx
    -- hx : x ∈ f ⁻¹' ⋂ (i : I), B i
    -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i
    apply mem_iInter_of_mem
    -- ⊢ ∀ (i : I), x ∈ f ⁻¹' B i
    intro i
    -- i : I
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_preimage]
    -- ⊢ f x ∈ B i
    rw [mem_preimage] at hx
    -- hx : f x ∈ ⋂ (i : I), B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), f x ∈ B i
    exact hx i
  . -- ⊢ x ∈ ⋂ (i : I), f ⁻¹' B i → x ∈ f ⁻¹' ⋂ (i : I), B i
    intro hx
    -- hx : x ∈ ⋂ (i : I), f ⁻¹' B i
    -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i
    rw [mem_preimage]
    -- ⊢ f x ∈ ⋂ (i : I), B i
    rw [mem_iInter]
    -- ⊢ ∀ (i : I), f x ∈ B i
    intro i
    -- i : I
    -- ⊢ f x ∈ B i
    rw [←mem_preimage]
    -- ⊢ x ∈ f ⁻¹' B i
    rw [mem_iInter] at hx
    -- hx : ∀ (i : I), x ∈ f ⁻¹' B i
    exact hx i

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by
  ext x
  -- ⊢ x ∈ f ⁻¹' ⋂ (i : I), B i ↔ x ∈ ⋂ (i : I), f ⁻¹' B i
  simp

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext ; simp }

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (s : Set β)
-- variable (A : I → Set α)
-- variable (a b : Prop)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (mem_iInter : x ∈ ⋂ i, A i ↔ ∀ i, x ∈ A i)
-- #check (mem_iInter_of_mem : (∀ i, x ∈ A i) → x ∈ ⋂ i, A i)
-- #check (mem_preimage : x ∈ f ⁻¹' s ↔ f x ∈ s)
