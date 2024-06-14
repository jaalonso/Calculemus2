-- Las_funciones_con_inversa_son_biyectivas.lean
-- Las funciones con inversa son biyectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4 se puede definir que g es una inversa de f por
--    def inversa (f : X → Y) (g : Y → X) :=
--      (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
-- y que f tiene inversa por
--    def tiene_inversa (f : X → Y) :=
--      ∃ g, inversa g f
--
-- Demostrar que si la función f tiene inversa, entonces f es biyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que f tiene inversa, existe una g: Y → X tal que
--    (∀x)[(g ∘ f)(x) = x]                                           (1)
--    (∀y)[(f ∘ g)(y) = y]                                           (2)
--
-- Para demostrar que f es inyectiva, sean a, b ∈ X tales que
--    f(a) = f(b)                                                    (3)
-- entonces
--    a = g(f(a))    [por (1)]
--      = g(f(b))    [por (3)]
--      = b          [por (1)]
--
-- Para demostrar que f es suprayectiva, sea y ∈ Y. Entonces, existe
-- a = g(y) ∈ X tal que
--    f(a) = f(g(y))
--         = y          [por (2)]
--
-- Como f es inyectiva y suprayectiva, entonces es biyectiva.

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
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  -- g : Y → X
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  constructor
  . -- ⊢ Injective f
    intros a b hab
    -- a b : X
    -- hab : f a = f b
    -- ⊢ a = b
    calc a = g (f a) := (h2 a).symm
         _ = g (f b) := congr_arg g hab
         _ = b       := h2 b
  . -- ⊢ Surjective f
    intro y
    -- y : Y
    -- ⊢ ∃ a, f a = y
    use g y
    -- ⊢ f (g y) = y
    exact h1 y

-- 2ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  -- g : Y → X
  -- h1 : ∀ (x : Y), (f ∘ g) x = x
  -- h2 : ∀ (y : X), (g ∘ f) y = y
  constructor
  . -- ⊢ Injective f
    intros a b hab
    -- a b : X
    -- hab : f a = f b
    -- ⊢ a = b
    calc a = g (f a) := (h2 a).symm
         _ = g (f b) := congr_arg g hab
         _ = b       := h2 b
  . -- ⊢ Surjective f
    intro y
    -- y : Y
    -- ⊢ ∃ a, f a = y
    exact ⟨g y, h1 y⟩

-- 3ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  constructor
  . exact LeftInverse.injective h2
  . exact RightInverse.surjective h1

-- 4ª demostración
-- ===============

example
  (hf : tiene_inversa f)
  : Bijective f :=
by
  rcases hf with ⟨g, ⟨h1, h2⟩⟩
  exact ⟨LeftInverse.injective h2,
         RightInverse.surjective h1⟩

-- 5ª demostración
-- ===============

example :
  tiene_inversa f → Bijective f :=
by
  rintro ⟨g, ⟨h1, h2⟩⟩
  exact ⟨LeftInverse.injective h2,
         RightInverse.surjective h1⟩

-- 6ª demostración
-- ===============

example :
  tiene_inversa f → Bijective f :=
fun ⟨_, ⟨h1, h2⟩⟩ ↦ ⟨LeftInverse.injective h2,
                     RightInverse.surjective h1⟩

-- Lemas usados
-- ============

-- variable (x y : X)
-- variable (g : Y → X)
-- #check (congr_arg f : x = y → f x = f y)
-- #check (LeftInverse.injective : LeftInverse g f → Injective f)
-- #check (RightInverse.surjective : RightInverse g f → Surjective f)
