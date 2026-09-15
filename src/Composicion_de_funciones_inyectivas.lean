-- Composicion_de_funciones_inyectivas.lean
-- La composición de funciones inyectivas es inyectiva
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la composición de funciones inyectivas es inyectiva.
-- ---------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- ---------------------
--
-- Tenemos que demostrar que
--    (∀ x, y) [(g ∘ f)(x) = (g ∘ f)(y) → x = y]
-- Sean x, y tales que
--    (g ∘ f)(x) = (g ∘ f)(y)                                        (1)
-- y tenemos que demostrar que
--    x = y                                                          (2)
-- El objetivo (2), usando que f es inyectiva, se reduce a
--    f(x) = f(y)
-- que, usando que g es inyectiva, se reduce a
--    g(f(x)) = g(f(y))
-- que, por la definición de la composición, coincide con (1).
--
-- 2ª demostración en LN
-- ---------------------
--
-- Tenemos que demostrar que
--    (∀ x, y) [(g ∘ f)(x) = (g ∘ f)(y) → x = y]
-- Sean x, y tales que
--    (g ∘ f)(x) = (g ∘ f)(y)
-- Entonces, por la definición de la composición,
--    g(f(x)) = g(f(y))
-- y, ser g inyectiva,
--    f(x) = f(y)
-- y, ser f inyectiva,
--    x = y

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Function

variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

-- 1ª demostración (basada en la 1ª en LN)
-- =======================================

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intros x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  apply hf
  -- ⊢ f x = f y
  apply hg
  -- ⊢ g (f x) = g (f y)
  exact h

-- 2ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intros x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  apply hf
  -- ⊢ f x = f y
  apply hg h

-- 3ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intros x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  exact hf (hg h)

-- 4ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
fun _ _ h => hf (hg h)

-- 5ª demostración (basada en la 2ª en LN)
-- =======================================

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro x y h1
  -- x y : α
  -- h1 : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  have h2 : g (f x) = g (f y) := h1
  have h3 : f x = f y := hg h2
  exact hf h3

-- 6ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro x y h1
  -- x y : α
  -- h1 : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  have h3 : f x = f y := hg h1
  exact hf h3

-- 7ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  -- ⊢ x = y
  exact hf (hg h)

-- 8ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
fun _ _ h ↦ hf (hg h)

-- 9ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by simp_all

-- 10ª demostración
-- ===============

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
Injective.comp hg hf

-- Lemas usados
-- ============

#check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
