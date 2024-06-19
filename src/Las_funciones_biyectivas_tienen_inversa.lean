-- Las_funciones_biyectivas_tienen_inversa.lean
-- Las funciones biyectivas tienen inversa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
-- y que f tiene inversa por
--    def tiene_inversa (f : X → Y) :=
--      ∃ g, inversa f g
--
-- Demostrar que si la función f es biyectiva, entonces f tiene inversa.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f: X → Y biyectiva. Entonces, f es suprayectiva y se puede
-- definir la función g: Y → X tal que
--    g(y) = x, donde x es un elemento de X tal que f(x) = y
-- Por tanto,
--    (∀y ∈ Y)[f(g(y)) = y]                                          (1)
--
-- Veamos que g es inversa de f; es decir, que se verifican
--    (∀y ∈ Y)[(f ∘ g) y = y]                                        (2)
--    (∀x ∈ X)[(g ∘ f) x = x]                                        (3)
--
-- La propiedad (2) se tiene por (1) y la definición de composición.
--
-- Para demostrar (3), sea x ∈ X. Entonces, por (1),
--    f(g(f(x))) = f(x)
-- y, por ser f inyectiva,
--    g(f(x)) = x
-- Luego,
--    (g ∘ f)(x) = x

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

variable {X Y : Type _}
variable (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

-- 1ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  constructor
  . -- ⊢ ∀ (x : Y), (f ∘ g) x = x
    exact hg
  . -- ⊢ ∀ (y : X), (g ∘ f) y = y
    intro a
    -- a : X
    -- ⊢ (g ∘ f) a = a
    rw [comp_apply]
    -- ⊢ g (f a) = a
    apply hfiny
    -- ⊢ f (g (f a)) = f a
    rw [hg (f a)]

-- 2ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
    -- hfiny : Injective f
    -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  constructor
  . -- ⊢ ∀ (x : Y), (f ∘ g) x = x
    exact hg
  . -- ⊢ ∀ (y : X), (g ∘ f) y = y
    intro a
    -- a : X
    -- ⊢ (g ∘ f) a = a
    exact @hfiny (g (f a)) a (hg (f a))

-- 3ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  use g
  -- ⊢ inversa g f
  exact ⟨hg, fun a ↦ @hfiny (g (f a)) a (hg (f a))⟩

-- 4ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  rcases hf with ⟨hfiny, hfsup⟩
  -- hfiny : Injective f
  -- hfsup : Surjective f
  choose g hg using hfsup
  -- g : Y → X
  -- hg : ∀ (b : Y), f (g b) = b
  exact ⟨g, ⟨hg, fun a ↦ @hfiny (g (f a)) a (hg (f a))⟩⟩

-- 5ª demostración
-- ===============

example
  (hf : Bijective f)
  : tiene_inversa f :=
by
  cases' (bijective_iff_has_inverse.mp hf) with g hg
  -- g : Y → X
  -- hg : LeftInverse g f ∧ Function.RightInverse g f
  aesop (add norm unfold [tiene_inversa, inversa])

-- Lemas usados
-- ============

-- variable (g : Y → X)
-- variable (x : X)
-- #check (bijective_iff_has_inverse : Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f)
-- #check (comp_apply : (g ∘ f) x = g (f x))
