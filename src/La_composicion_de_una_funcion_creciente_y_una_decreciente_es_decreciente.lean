-- La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean
-- La composición de una función creciente y una decreciente es decreciente
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea una función f de ℝ en ℝ. Se dice que f es creciente si para todo
-- x e y tales que x ≤ y se tiene que f(x) ≤ f(y). Se dice que f es
-- decreciente si para todo x e y tales que x ≤ y se tiene que
-- f(x) ≥ f(y).
--
-- Demostrar con Lean4 que si f es creciente y g es decreciente,
-- entonces (g ∘ f) es decreciente.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ ℝ tales que x ≤ y. Entonces, por ser f creciente,
--    f(x) ≥ f(y)
-- y, por ser g decreciente,
--    g(f(x)) ≤ g(f(y)).
-- Por tanto,
--    (g ∘ f)(x) ≤ (g ∘ f)(y).

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
  ∀ {x y}, x ≤ y → f x ≥ f y

-- 1ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intro x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  have h1 : f x ≤ f y := hf h
  show (g ∘ f) x ≥ (g ∘ f) y
  exact hg h1

-- 2ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intro x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  show (g ∘ f) x ≥ (g ∘ f) y
  exact hg (hf h)

-- 3ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
fun {_ _} h ↦ hg (hf h)

-- 4ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y hxy
  calc (g ∘ f) x
       = g (f x)   := rfl
     _ ≥ g (f y)   := hg (hf hxy)
     _ = (g ∘ f) y := rfl

-- 5ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  unfold creciente decreciente at *
  -- hf : ∀ {x y : ℝ}, x ≤ y → f x ≤ f y
  -- hg : ∀ {x y : ℝ}, x ≤ y → g x ≥ g y
  -- ⊢ ∀ {x y : ℝ}, x ≤ y → (g ∘ f) x ≥ (g ∘ f) y
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  unfold Function.comp
  -- ⊢ g (f x) ≥ g (f y)
  apply hg
  -- ⊢ f x ≤ f y
  apply hf
  -- ⊢ x ≤ y
  exact h

-- 6ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  apply hg
  -- ⊢ f x ≤ f y
  apply hf
  -- ⊢ x ≤ y
  exact h

-- 7ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  apply hg
  -- ⊢ f x ≤ f y
  exact hf h

-- 8ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by
  intros x y h
  -- x y : ℝ
  -- h : x ≤ y
  -- ⊢ (g ∘ f) x ≥ (g ∘ f) y
  exact hg (hf h)

-- 9ª demostración
-- ===============

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
by tauto
