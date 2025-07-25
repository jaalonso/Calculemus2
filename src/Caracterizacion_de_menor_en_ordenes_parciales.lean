-- Caracterizacion_de_menor_en_ordenes_parciales.lean
-- En los órdenes parciales, a < b ↔ a ≤ b ∧ a ≠ b.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 03-enero-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en un orden parcial
--     a < b ↔ a ≤ b ∧ a ≠ b
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos los siguientes lemas
--    (∀ a, b)[a < b ↔ a ≤ b ∧ b ≰ a]                               (L1)
--    (∀ a, b)[a ≤ b → b ≤ a → a = b]                               (L2)
--
-- Por el lema L1, lo que tenemos que demostrar es
--    a ≤ b ∧ b ≰ a ↔ a ≤ b ∧ a ≠ b
-- Lo haremos demostrando las dos implicaciones.
--
-- (⇒) Supongamos que a ≤ b y b ≰ a. Tenemos que demostrar que
-- a ≠ b. Lo haremos por reducción al absurdo. Para ello, supongamos que
-- a = b. Entonces, b ≤ a que contradice a b ≰ a.
--
-- (⇐) Supongamos que a ≤ b y a ≠ b. Tenemos que demostrar que
-- b ≰ a. Lo haremos por reducción al absurdo. Para ello, supongamos que
-- b ≤ a. Entonces, junto con a ≤ b, se tiene que a = b que es una
-- contradicicción con a ≠ b.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {α : Type _} [PartialOrder α]
variable (a b : α)

-- 1ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  constructor
  . -- ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    rintro ⟨h1 : a ≤ b, h2 : ¬b ≤ a⟩
    -- ⊢ a ≤ b ∧ a ≠ b
    constructor
    . -- ⊢ a ≤ b
      exact h1
    . -- ⊢ a ≠ b
      rintro (h3 : a = b)
      -- ⊢ False
      have h4: b = a := h3.symm
      have h5: b ≤ a := le_of_eq h4
      show False
      exact h2 h5
  . -- ⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    rintro ⟨h5 : a ≤ b , h6 : a ≠ b⟩
    -- ⊢ a ≤ b ∧ ¬b ≤ a
    constructor
    . -- ⊢ a ≤ b
      exact h5
    . -- ⊢ ¬b ≤ a
      rintro (h7 : b ≤ a)
      have h8 : a = b := le_antisymm h5 h7
      show False
      exact h6 h8

-- 2ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  constructor
  . -- ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    rintro ⟨h1 : a ≤ b, h2 : ¬b ≤ a⟩
    -- ⊢ a ≤ b ∧ a ≠ b
    constructor
    . -- ⊢ a ≤ b
      exact h1
    . -- ⊢ a ≠ b
      rintro (h3 : a = b)
      -- ⊢ False
      exact h2 (le_of_eq h3.symm)
  . -- ⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    rintro ⟨h4 : a ≤ b , h5 : a ≠ b⟩
    -- ⊢ a ≤ b ∧ ¬b ≤ a
    constructor
    . -- ⊢ a ≤ b
      exact h4
    . -- ⊢ ¬b ≤ a
      rintro (h6 : b ≤ a)
      exact h5 (le_antisymm h4 h6)

-- 3ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  constructor
  . -- ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    rintro ⟨h1 : a ≤ b, h2 : ¬b ≤ a⟩
    -- ⊢ a ≤ b ∧ a ≠ b
    constructor
    . -- ⊢ a ≤ b
      exact h1
    . -- ⊢ a ≠ b
      exact fun h3 ↦ h2 (le_of_eq h3.symm)
  . -- ⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    rintro ⟨h4 : a ≤ b , h5 : a ≠ b⟩
    -- ⊢ a ≤ b ∧ ¬b ≤ a
    constructor
    . -- ⊢ a ≤ b
      exact h4
    . -- ⊢ ¬b ≤ a
      exact fun h6 ↦ h5 (le_antisymm h4 h6)

-- 4ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  constructor
  . -- ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    rintro ⟨h1 : a ≤ b, h2 : ¬b ≤ a⟩
    -- ⊢ a ≤ b ∧ a ≠ b
    exact ⟨h1, fun h3 ↦ h2 (le_of_eq h3.symm)⟩
  . -- ⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    rintro ⟨h4 : a ≤ b , h5 : a ≠ b⟩
    -- ⊢ a ≤ b ∧ ¬b ≤ a
    exact ⟨h4, fun h6 ↦ h5 (le_antisymm h4 h6)⟩

-- 5ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  constructor
  . -- ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    exact fun ⟨h1, h2⟩ ↦ ⟨h1, fun h3 ↦ h2 (le_of_eq h3.symm)⟩
  . -- ⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    exact fun ⟨h4, h5⟩ ↦ ⟨h4, fun h6 ↦ h5 (le_antisymm h4 h6)⟩

-- 6ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  rw [lt_iff_le_not_ge]
  -- ⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun h3 ↦ h2 (le_of_eq h3.symm)⟩,
         fun ⟨h4, h5⟩ ↦ ⟨h4, fun h6 ↦ h5 (le_antisymm h4 h6)⟩⟩

-- 7ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
by
  constructor
  . -- ⊢ a < b → a ≤ b ∧ a ≠ b
    intro h
    -- h : a < b
    -- ⊢ a ≤ b ∧ a ≠ b
    constructor
    . -- ⊢ a ≤ b
      exact le_of_lt h
    . -- ⊢ a ≠ b
      exact ne_of_lt h
  . -- ⊢ a ≤ b ∧ a ≠ b → a < b
    rintro ⟨h1, h2⟩
    -- h1 : a ≤ b
    -- h2 : a ≠ b
    -- ⊢ a < b
    exact lt_of_le_of_ne h1 h2

-- 8ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨le_of_lt h, ne_of_lt h⟩,
   fun ⟨h1, h2⟩ ↦ lt_of_le_of_ne h1 h2⟩

-- 9ª demostración
-- ===============

example : a < b ↔ a ≤ b ∧ a ≠ b :=
  lt_iff_le_and_ne

-- Lemas usados
-- ============

-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_of_eq : a = b → a ≤ b)
-- #check (lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b)
-- #check (lt_iff_le_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a)
-- #check (lt_of_le_of_ne : a ≤ b → a ≠ b → a < b)
