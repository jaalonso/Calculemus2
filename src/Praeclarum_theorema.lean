-- Praeclarum_theorema.lean
-- Praeclarum theorema
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, January 21, 2025
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove the [praeclarum theorema](https://tinyurl.com/25yt3ef9) of
-- Leibniz:
--    (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s))
-- ---------------------------------------------------------------------

import Mathlib.Tactic

variable (p q r s : Prop)

-- Proof 1
-- =======

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  constructor
  . -- q
    exact hpq hp
  . -- s
    exact hrs hr

-- Proof 2
-- =======

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by
  intro ⟨hpq, hrs⟩ ⟨hp, hr⟩
  -- hpq : p → q
  -- hrs : r → s
  -- hp : p
  -- hr : r
  exact ⟨hpq hp, hrs hr⟩

-- Proof 3
-- =======

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ ⟨hp, hr⟩ ↦ ⟨hpq hp, hrs hr⟩

-- Proof 4
-- =======

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
fun ⟨hpq, hrs⟩ hpr ↦ And.imp hpq hrs hpr

-- Proof 5
-- =======

example:
  (p → q) ∧ (r → s) → ((p ∧ r) → (q ∧ s)) :=
by aesop
