-- Propiedad_transitiva_del_subconjunto.lean
-- Si r ⊆ s y s ⊆ t, entonces r ⊆ t.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si r ⊆ s y s ⊆ t, entonces r ⊆ t.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural (LN)
-- =====================================

-- 1ª demostración en LN
-- ---------------------

-- Tenemos que demostrar que
--    (∀ x) [x ∈ r → x ∈ t]
-- Sea x tal que
--    x ∈ r.
-- Puesto que r ⊆ s, se tiene que
--    x ∈ s
-- y, puesto que s ⊆ t, se tiene que
--    x ∈ t
-- que es lo que teníamos que demostrar.

-- 2ª demostración en LN
-- ---------------------

-- Tenemos que demostrar que
--    (∀ x) [x ∈ r → x ∈ t]
-- Sea x tal que
--    x ∈ r
-- Tenemos que demostrar que
--    x ∈ t
-- que, puesto que s ⊆ t, se reduce a
--    x ∈ s
-- que, puesto que r ⊆ s, se redece a
--    x ∈ r
-- que es lo que hemos supuesto.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

open Set

variable {α : Type _}
variable (r s t : Set α)

-- 1ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by
  intros x xr
  -- xr : x ∈ r
  have xs : x ∈ s := rs xr
  show x ∈ t
  exact st xs

-- 2ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by
  intros x xr
  -- x : α
  -- xr : x ∈ r
  apply st
  -- ⊢ x ∈ s
  apply rs
  -- ⊢ x ∈ r
  exact xr

-- 3ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
fun _ xr ↦ st (rs xr)

-- 4ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by exact?
Subset.trans rs st

-- 5ª demostración
example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
by tauto

-- Lemas usados
-- ============

-- #check (Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t)
