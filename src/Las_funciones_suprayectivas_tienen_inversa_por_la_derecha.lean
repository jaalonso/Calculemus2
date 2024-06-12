-- Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.lean
-- Las funciones suprayectivas tienen inversa por la derecha.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, que g es una inversa por la izquierda de f está definido
-- por
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
-- Demostrar que si f es una función suprayectiva, entonces f tiene
-- inversa por la derecha.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f: A → B una función suprayectiva. Sea g: B → A la función
-- definida por
--    g(y) = x, donde x es un elemento tal que f(x) = y
--
-- Veamos que g es una inversa por la derecha de f; es decir,
--    (∀y ∈ B)[f(g(y)) = y
-- Para ello, sea b ∈ B. Entonces,
--    f(g(b)) = f(a)
-- donde a es un elemento tal que
--    f(a) = b
-- Por tanto,
--    f(g(b)) = b

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function Classical

variable {α β: Type _}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  unfold HasRightInverse
  -- ⊢ ∃ finv, Function.RightInverse finv f
  let g := fun y ↦ Classical.choose (hf y)
  use g
  -- ⊢ Function.RightInverse g f
  unfold Function.RightInverse
  -- ⊢ LeftInverse f g
  unfold Function.LeftInverse
  -- ⊢ ∀ (x : β), f (g x) = x
  intro b
  -- ⊢ f (g b) = b
  exact Classical.choose_spec (hf b)

-- 2ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  let g := fun y ↦ Classical.choose (hf y)
  use g
  -- ⊢ Function.RightInverse g f
  intro b
  -- ⊢ f (g b) = b
  exact Classical.choose_spec (hf b)

-- 3ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  use surjInv hf
  -- ⊢ Function.RightInverse (surjInv hf) f
  intro b
  -- ⊢ f (surjInv hf b) = b
  exact surjInv_eq hf b

-- 4ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
by
  use surjInv hf
  -- ⊢ Function.RightInverse (surjInv hf) f
  exact surjInv_eq hf

-- 5ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
⟨surjInv hf, surjInv_eq hf⟩

-- 6ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
⟨_, rightInverse_surjInv hf⟩

-- 7ª demostración
-- ===============

example
  (hf : Surjective f)
  : HasRightInverse f :=
Surjective.hasRightInverse hf

-- Lemas usados
-- ============

-- variable (p : α -> Prop)
-- #check (Classical.choose_spec : (h : ∃ x, p x) → p (Classical.choose h))
--
-- variable (h : Surjective f)
-- variable (b : β)
-- #check (surjInv_eq h b : f (surjInv h b) = b)
-- #check (rightInverse_surjInv h : RightInverse (surjInv h) f)
--
-- #check (Surjective.hasRightInverse : Surjective f → HasRightInverse f)
