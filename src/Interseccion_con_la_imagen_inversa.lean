-- Interseccion_con_la_imagen_inversa.lean
-- Intersección con la imagen.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-abril-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemmos que demostrar que, para todo y,
--    y ∈ f[s] ∩ v ↔ y ∈ f[s ∩ f⁻¹[v]]
-- Lo haremos demostrando las sod implicaciones.
--
-- (⟹) Supongamos que y ∈ f[s] ∩ v. Entonces,
--    y ∈ f[s]                                                       (1)
--    y ∈ v                                                          (2)
-- Por (1), existe un x tal que
--    x ∈ s                                                          (3)
--    f(x) = y                                                       (4)
-- De (2) y (4), se tiene que
--    f(x) ∈ v
-- y, por tanto,
--    x ∈ f⁻¹[v]                                                     (5)
-- De (3) y (5), se tiene que
--    x ∈ s ∩ f⁻¹[v]
-- Por tanto,
--    f(x) ∈ f[s ∩ f⁻¹[v]]
-- y, por (4),
--    y ∈ f[s ∩ f⁻¹[v]]
--
-- (⟸) Supongamos que y ∈ f[s ∩ f⁻¹[v]]. Entonces, existe un x tal que
--    x ∈ s ∩ f⁻¹[v]                                                 (6)
--    f(x) = y                                                       (7)
-- Por (6), se tiene que
--    x ∈ s                                                          (8)
--    x ∈ f⁻¹[v]                                                     (9)
-- Por (8), se tiene que
--    f(x) ∈ f[s]
-- y, por (7),
--    y ∈ f[s]                                                      (10)
-- Por (9),
--    f(x) ∈ v
-- y, por (7),
--    y ∈ v                                                         (11)
-- Por (10) y (11),
--    y ∈ f[s] ∩ v

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    cases' hy with hyfs yv
    -- hyfs : y ∈ f '' s
    -- yv : y ∈ v
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    have h1 : f x ∈ v := by rwa [←fxy] at yv
    have h3 : x ∈ s ∩ f ⁻¹' v := mem_inter xs h1
    have h4 : f x ∈ f '' (s ∩ f ⁻¹' v) := mem_image_of_mem f h3
    show y ∈ f '' (s ∩ f ⁻¹' v)
    rwa [fxy] at h4
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y
    cases' hx with hx1 fxy
    -- hx1 : x ∈ s ∩ f ⁻¹' v
    -- fxy : f x = y
    cases' hx1 with xs xfv
    -- xs : x ∈ s
    -- xfv : x ∈ f ⁻¹' v
    have h5 : f x ∈ f '' s := mem_image_of_mem f xs
    have h6 : y ∈ f '' s := by rwa [fxy] at h5
    have h7 : f x ∈ v := mem_preimage.mp xfv
    have h8 : y ∈ v := by rwa [fxy] at h7
    show y ∈ f '' s ∩ v
    exact mem_inter h6 h8

-- 2ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    cases' hy with hyfs yv
    -- hyfs : y ∈ f '' s
    -- yv : y ∈ v
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ y ∈ f '' s
      use x
      -- ⊢ x ∈ s ∧ f x = y
      constructor
      . -- ⊢ x ∈ s
        exact hx.1.1
      . -- ⊢ f x = y
        exact hx.2
    . -- ⊢ y ∈ v
      cases' hx with hx1 fxy
      -- hx1 : x ∈ s ∩ f ⁻¹' v
      -- fxy : f x = y
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact hx1.2

-- 3ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . exact fxy
  . rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    constructor
    . -- ⊢ y ∈ f '' s
      use x, xs
    . -- ⊢ y ∈ v
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact xv

-- 4ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    aesop
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    aesop

-- 5ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by ext ; constructor <;> aesop

-- 6ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
(image_inter_preimage f s v).symm

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Set α)
-- #check (image_inter_preimage f s v : f '' (s ∩ f ⁻¹' v) = f '' s ∩ v)
-- #check (mem_image_of_mem  f : x ∈ a → f x ∈ f '' a)
-- #check (mem_inter : x ∈ a → x ∈ b → x ∈ a ∩ b)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
