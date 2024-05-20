-- Una_funcion_creciente_e_involutiva_es_la_identidad.lean
-- Si una función es creciente e involutiva, entonces es la identidad
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea una función f de ℝ en ℝ.
-- + Se dice que f es creciente si para todo x e y tales que x ≤ y se
--   tiene que f(x) ≤ f(y).
-- + Se dice que f es involutiva si para todo x se tiene que f(f(x)) = x.
--
-- En Lean4 que f sea creciente se representa por `Monotone f` y que sea
-- involutiva por `Involutive f`
--
-- Demostrar con Lean4 que si f es creciente e involutiva, entonces f es
-- la identidad.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para todo x ∈ ℝ, f(x) = x. Sea x ∈ ℝ.
-- Entonces, por ser f involutiva, se tiene que
--    f(f(x)) = x                                                    (1)
-- Además, por las propiedades del orden, se tiene que f(x) ≤ x ó
-- x ≤ f(x). Demostraremos que f(x) = x en los dos casos.
--
-- Caso 1: Supongamos que
--    f(x) ≤ x                                                       (2)
-- Entonces, por ser f creciente, se tiene que
--    f(f(x)) ≤ f(x)                                                 (3)
-- Sustituyendo (1) en (3), se tiene
--    x ≤ f(x)
-- que junto con (1) da
--    f(x) = x
--
-- Caso 2: Supongamos que
--    x ≤ f(x)                                                       (4)
-- Entonces, por ser f creciente, se tiene que
--    f(x) ≤ f(f(x))                                                 (5)
-- Sustituyendo (1) en (5), se tiene
--    f(x) ≤ x
-- que junto con (4) da
--    f(x) = x

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
open Function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  have h : f (f x) = x := hi x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    have h1a : f (f x) ≤ f x := hc h1
    have h1b : x ≤ f x := by rwa [h] at h1a
    show f x = x
    exact antisymm h1 h1b
  . -- h2 : x ≤ f x
    have h2a : f x ≤ f (f x) := hc h2
    have h2b : f x ≤ x := by rwa [h] at h2a
    show f x = x
    exact antisymm h2b h2

-- 2ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  unfold Monotone Involutive at *
  -- hc : ∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b
  -- hi : ∀ (x : ℝ), f (f x) = x
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  unfold id
  -- ⊢ f x = x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    have h3 : f (f x) ≤ f x := by
      apply hc
      -- ⊢ f x ≤ x
      exact h1
    rwa [hi] at h3
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    have h4 : f x ≤ f (f x) := by
      apply hc
      -- ⊢ x ≤ f x
      exact h2
    rwa [hi] at h4

-- 3ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    have h3 : f (f x) ≤ f x := hc h1
    rwa [hi] at h3
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    have h4 : f x ≤ f (f x) := hc h2
    rwa [hi] at h4

-- 4ª demostración
example
  (hc : Monotone f)
  (hi : Involutive f)
  : f = id :=
by
  funext x
  -- x : ℝ
  -- ⊢ f x = id x
  cases' (le_total (f x) x) with h1 h2
  . -- h1 : f x ≤ x
    apply antisymm h1
    -- ⊢ x ≤ f x
    calc x
         = f (f x) := (hi x).symm
       _ ≤ f x     := hc h1
  . -- h2 : x ≤ f x
    apply antisymm _ h2
    -- ⊢ f x ≤ x
    calc f x
         ≤ f (f x) := hc h2
       _ = x       := hi x

-- Lemas usados
-- ============

-- variable (a b : ℝ)
-- #check (le_total a b : a ≤ b ∨ b ≤ a)
-- #check (antisymm : a ≤ b → b ≤ a → a = b)
