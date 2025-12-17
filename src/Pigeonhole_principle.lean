-- Pigeonhole_principle.lean
-- Pigeonhole principle.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, October 7, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove the pigeonhole principle; that is, if S is a finite set and T
-- and U are subsets of S such that the number of elements of S is less
-- than the sum of the number of elements of T and U, then the
-- intersection of T and U is non-empty.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- By contradiction. For this, let's assume that
--    T ∩ U = ∅                                                      (1)
-- and we have to prove that
--    card(T) + card(U) ≤ card(S)                                    (2)

-- The inequality (2) is proved by the following chain of relations:
--    card(T) + card(U) = card(T ∪ U) + card(T ∩ U)
--                      = card(T ∪ U) + 0           [by (1)]
--                      = card(T ∪ U)
--                      ≤ card(S)                   [because T ⊆ S and U ⊆ S]

-- Proofs with Lean4
-- =================

import Mathlib.Data.Finset.Card

open Finset

variable [DecidableEq α]
variable {s t u : Finset α}

set_option pp.fieldNotation false

-- Proof 1
-- =======

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  have h2 : card (t ∩ u) = 0 := card_eq_zero.mpr hstu
  calc
    card t + card u
      = card (t ∪ u) + card (t ∩ u) := (card_union_add_card_inter t u).symm
    _ = card (t ∪ u) + 0            := congrArg (card (t ∪ u) + .) h2
    _ = card (t ∪ u)                := Nat.add_zero (card (t ∪ u))
    _ ≤ card s                      := card_le_card (union_subset hts hus)

-- Proof 2
-- =======

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  calc
    card t + card u
      = card (t ∪ u) + card (t ∩ u) :=
          (card_union_add_card_inter t u).symm
    _ = card (t ∪ u) + 0 :=
          congrArg (card (t ∪ u) + .) (card_eq_zero.mpr hstu)
    _ = card (t ∪ u) :=
          Nat.add_zero (card (t ∪ u))
    _ ≤ card s :=
          card_le_card (union_subset hts hus)

-- Proof 3
-- =======

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
by
  contrapose! hstu
  -- hstu : ¬Finset.Nonempty (t ∩ u)
  -- ⊢ card t + card u ≤ card s
  calc
    card t + card u
      = card (t ∪ u) := by simp [← card_union_add_card_inter, hstu]
    _ ≤ card s       := by gcongr; exact union_subset hts hus

-- Proof 4
-- =======

example
  (hts : t ⊆ s)
  (hus : u ⊆ s)
  (hstu : card s < card t + card u)
  : Finset.Nonempty (t ∩ u) :=
inter_nonempty_of_card_lt_card_add_card hts hus hstu

-- Used lemmas
-- ===========

variable (a : ℕ)
#check (Nat.add_zero a : a + 0 = a)
#check (card_eq_zero : card s = 0 ↔ s = ∅)
#check (card_le_card : s ⊆ t → card s ≤ card t)
#check (card_union_add_card_inter s t : card (s ∪ t) + card (s ∩ t) =card s + card t)
#check (inter_nonempty_of_card_lt_card_add_card : t ⊆ s → u ⊆ s → card s < card t + card u → Finset.Nonempty (t ∩ u))
#check (not_nonempty_iff_eq_empty : ¬Finset.Nonempty s ↔ s = ∅)
#check (union_subset : s ⊆ u → t ⊆ u → s ∪ t ⊆ u)
