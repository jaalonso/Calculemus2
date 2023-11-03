-- Composicion_de_suprayectivas.lean
-- La composición de funciones suprayectivas es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de funciones suprayectivas es
-- suprayectiva.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que f : A → B y g : B → C son suprayectivas. Tenemos que
-- demostrar que
--     (∀z ∈ C)(∃x ∈ A)[g(f(x)) = z]
-- Sea z ∈ C. Por ser g suprayectiva, existe un y ∈ B tal que
--     g(y) = z                                                      (1)
-- Por ser f suprayectiva, existe un x ∈ A tal que
--     f(x) = y                                                      (2)
-- Por tanto,
--     g(f(x)) = g(y)   [por (2)]
--             = z      [por (1)]

-- Demostraciones con lean4
-- ========================

import Mathlib.Tactic
open Function
variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

-- 1ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  use x
  -- ⊢ (g ∘ f) x = z
  dsimp
  -- ⊢ g (f x) = z
  rw [hx]
  -- ⊢ g y = z
  exact hy

-- 2ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  use x
  -- ⊢ (g ∘ f) x = z
  dsimp
  -- ⊢ g (f x) = z
  rw [hx, hy]

-- 3ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  exact ⟨x, by dsimp ; rw [hx, hy]⟩

-- 4ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  rcases hg z with ⟨y, hy : g y = z⟩
  rcases hf y with ⟨x, hx : f x = y⟩
  exact ⟨x, by dsimp ; rw [hx, hy]⟩

-- 5ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
Surjective.comp hg hf

-- Lemas usados
-- ============

-- #check (Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f))
