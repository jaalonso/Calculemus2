-- La_paradoja_del_barbero.lean
-- La paradoja del barbero.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar la paradoja del barbero https://bit.ly/3eWyvVw es decir,
-- que no existe un hombre que afeite a todos los que no se afeitan a sí
-- mismo y sólo a los que no se afeitan a sí mismo.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    ¬((∃ x)(∀ y)[afeita(x,y) ↔ ¬afeita(y,y)])
-- Para ello, supongamos que
--    (∃ x)(∀ y)[afeita(x,y) ↔ ¬afeita(y,y)]                         (1)
-- y tenemos que llegar a una contradicción.
--
-- Sea b un elemento que verifica (1); es decir,
--    (∀ y)[afeita(b,y) ↔ ¬afeita(y,y)]
-- Entonces,
--    afeita(b,b) ↔ ¬afeita(b,b)
-- que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

-- 1ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  specialize hb b
  -- hb : afeita b b ↔ ¬afeita b b
  by_cases h : afeita b b
  . -- h : afeita b b
    apply absurd h
    -- ⊢ ¬afeita b b
    exact hb.mp h
  . -- h : ¬afeita b b
    apply h
    -- ⊢ afeita b b
    exact hb.mpr h

-- 2ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  specialize hb b
  -- hb : afeita b b ↔ ¬afeita b b
  by_cases h : afeita b b
  . -- h : afeita b b
    exact (hb.mp h) h
  . -- h : ¬afeita b b
    exact h (hb.mpr h)

-- 3ª demostración
-- ===============

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
by
  intro h
  -- h : ∃ x, ∀ (y : Hombre), afeita x y ↔ ¬afeita y y
  -- ⊢ False
  cases' h with b hb
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  exact iff_not_self (hb b)

-- 4ª demostración
-- ===============

example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
by
  rintro ⟨b, hb⟩
  -- b : Hombre
  -- hb : ∀ (y : Hombre), afeita b y ↔ ¬afeita y y
  -- ⊢ False
  exact iff_not_self (hb b)

-- 5ª demostración
-- ===============

example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
fun ⟨b, hb⟩ ↦ iff_not_self (hb b)

-- Lemas usados
-- ============

-- variable (p q : Prop)
-- #check (absurd : p → (¬p → q))
-- #check (iff_not_self : ¬(p ↔ ¬p))
