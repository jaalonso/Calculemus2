-- Interseccion_de_los_primos_y_los_mayores_que_dos.lean
-- Los primos mayores que 2 son impares.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-marzo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Los números primos, los mayores que 2 y los impares se definen por
--    def Primos      : Set ℕ := {n | Nat.Prime n}
--    def MayoresQue2 : Set ℕ := {n | n > 2}
--    def Impares     : Set ℕ := {n | ¬Even n}
--
-- Demostrar que
--    Primos ∩ MayoresQue2 ⊆ Impares
-- ----------------------------------------------------------------------

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Nat

def Primos      : Set ℕ := {n | Nat.Prime n}
def MayoresQue2 : Set ℕ := {n | n > 2}
def Impares     : Set ℕ := {n | ¬Even n}

-- 1ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  intro n
  -- n : ℕ
  -- ⊢ n ∈ {n | Nat.Prime n} ∩ {n | n > 2} → n ∈ {n | ¬Even n}
  simp
  -- ⊢ Nat.Prime n → 2 < n → Odd n
  intro hn
  -- hn : Nat.Prime n
  -- ⊢ 2 < n → Odd n
  rcases Prime.eq_two_or_odd hn with (h | h)
  . -- h : n = 2
    rw [h]
    -- ⊢ 2 < 2 → ¬Even 2
    intro h1
    -- h1 : 2 < 2
    -- ⊢ Odd 2
    exfalso
    exact absurd h1 (lt_irrefl 2)
  . -- h : n % 2 = 1
    intro
    -- a : 2 < n
    -- ⊢ Odd n
    exact odd_iff.mpr h

-- 2ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  rintro n ⟨h1, h2⟩
  -- n : ℕ
  -- h1 : n ∈ {n | Nat.Prime n}
  -- h2 : n ∈ {n | n > 2}
  -- ⊢ n ∈ {n | ¬Even n}
  simp at *
  -- h1 : Nat.Prime n
  -- h2 : 2 < n
  -- ⊢ ¬Even n
  rcases Prime.eq_two_or_odd h1 with (h3 | h4)
  . -- h3 : n = 2
    rw [h3] at h2
    -- h2 : 2 < 2
    exfalso
    -- ⊢ False
    exact absurd h2 (lt_irrefl 2)
  . -- h4 : n % 2 = 1
    exact odd_iff.mpr h4

-- 3ª demostración
-- ===============

example : Primos ∩ MayoresQue2 ⊆ Impares :=
by
  unfold Primos MayoresQue2 Impares
  -- ⊢ {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬Even n}
  rintro n ⟨h1, h2⟩
  -- n : ℕ
  -- h1 : n ∈ {n | Nat.Prime n}
  -- h2 : n ∈ {n | n > 2}
  -- ⊢ n ∈ {n | ¬Even n}
  simp at *
  -- h1 : Nat.Prime n
  -- h2 : 2 < n
  -- ⊢ ¬Even n
  rcases Prime.eq_two_or_odd h1 with (h3 | h4)
  . -- h3 : n = 2
    rw [h3] at h2
    -- h2 : 2 < 2
    linarith
  . -- h4 : n % 2 = 1
    exact odd_iff.mpr h4

-- Lemas usados
-- ============

-- variable (p n : ℕ)
-- variable (a b : Prop)
-- #check (Prime.eq_two_or_odd : Nat.Prime p → p = 2 ∨ p % 2 = 1)
-- #check (absurd : a → ¬a → b)
-- #check (even_iff : Even n ↔ n % 2 = 0)
-- #check (lt_irrefl n : ¬n < n)
-- #check (one_ne_zero : 1 ≠ 0)
