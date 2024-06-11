-- Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.lean
-- Las funciones con inversa por la derecha son suprayectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, que g es una inversa por la izquierda de f está definido por
--    LeftInverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- que g es una inversa por la derecha de f está definido por
--    RightInverse (g : β → α) (f : α → β) : Prop :=
--       LeftInverse f g
-- y que f tenga inversa por la derecha está definido por
--    HasRightInverse (f : α → β) : Prop :=
--       ∃ g : β → α, RightInverse g f
-- Finalmente, que f es suprayectiva está definido por
--    def Surjective (f : α → β) : Prop :=
--       ∀ b, ∃ a, f a = b
--
-- Demostrar que si la función f tiene inversa por la derecha, entonces
-- f es suprayectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f: A → B y g: B → A una inversa por la derecha de f. Entonces,
--    (∀y ∈ B)[f(g(y)) = y]                                          (1)
--
-- Para demostrar que f es subprayectiva, sea b ∈ B. Entonces,
-- g(b) ∈ A y, por (1),
--    f(g(b) = b

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

variable {α β: Type _}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  unfold Surjective
  -- ⊢ ∀ (b : β), ∃ a, f a = b
  unfold HasRightInverse at hf
  -- hf : ∃ finv, Function.RightInverse finv f
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  use g b
  -- ⊢ f (g b) = b
  exact hg b

-- 2ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  use g b
  -- ⊢ f (g b) = b
  exact hg b

-- 3ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
by
  intro b
  -- b : β
  -- ⊢ ∃ a, f a = b
  cases' hf with g hg
  -- g : β → α
  -- hg : Function.RightInverse g f
  exact ⟨g b, hg b⟩

-- 4ª demostración
-- ===============

example
  (hf : HasRightInverse f)
  : Surjective f :=
HasRightInverse.surjective hf

-- Lemas usados
-- ============

-- #check (HasRightInverse.surjective : HasRightInverse f → Surjective f)
