-- Cota_inferior_de_sucesiones_convergentes.lean
-- Si a converge a L, entonces (∃ N)(∀ n ≥ N)[aₙ ≥ L - 1]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si la sucesión a es convergente, entonces a está
-- eventualmente acotadas inferiormente; es decir, si a converge a L,
-- entonces
--    (∃ N)(∀ n ≥ N)[aₙ ≥ L - 1]
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que a converge a L, existe un N ∈ ℕ tal que
--    (∀ n ≥ N) |aₙ - L| < 1                                          (1)
-- Veamos que
--    (∀ n ≥ N) [aₙ ≥ L - 1]
-- En efecto, sea n ≥ N. Por (1),
--    |aₙ - L| < 1
-- Luego,
--    -1 < aₙ - L ∧ aₙ - L < 1
--    ==> -1 < aₙ - L
--    ==> aₙ ≥ L - 1

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a : ℕ → ℝ}
variable {L : ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

variable (x : ℝ)

lemma L1
  (h : -1 < x)
  : 0 ≤ x + 1 :=
by
  have h1 : -1 + 1 < x + 1 := (add_lt_add_iff_right 1).mpr h
  have h2 : 0 < x + 1 := neg_lt_iff_pos_add.mp h
  exact le_of_lt h2

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
by
  obtain ⟨N, hN⟩ := ha 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  use N
  -- ⊢ ∀ n ≥ N, a n ≥ L - 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ a n ≥ L - 1
  have h1 : |a n - L| < 1 := hN n hn
  have h2 : -1 < a n - L ∧ a n - L < 1 := abs_lt.mp h1
  have h3 : -1 < a n - L := h2.1
  rw [ge_iff_le, ← sub_nonneg]
  -- ⊢ 0 ≤ a n - (L - 1)
  calc 0
     _ ≤ (a n - L) + 1 := L1 (a n - L) h3
     _ = a n - (L - 1) := sub_add (a n) L 1

-- 2ª demostración
-- ===============

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
by
  obtain ⟨N, hN⟩ := ha 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  use N
  -- ⊢ ∀ n ≥ N, a n ≥ L - 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ a n ≥ L - 1
  have h1 : -1 < a n - L := (abs_lt.mp (hN n hn)).1
  have h2 : a n - (L - 1) = (a n - L) + 1 := (sub_add (a n) L 1).symm
  rw [ge_iff_le, ← sub_nonneg]
  -- ⊢ 0 ≤ a n - (L - 1)
  rw [h2]
  -- ⊢ 0 ≤ a n - L + 1
  exact neg_le_iff_add_nonneg.mp (le_of_lt h1)

-- 3ª demostración
-- ===============

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
by
  obtain ⟨N, hN⟩ := ha 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  use N
  -- ⊢ ∀ n ≥ N, a n ≥ L - 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ a n ≥ L - 1
  have h1 : -1 < a n - L := (abs_lt.mp (hN n hn)).1
  rw [ge_iff_le, ← sub_nonneg]
  -- ⊢ 0 ≤ a n - (L - 1)
  calc 0
     _ ≤ (a n - L) + 1 := by grind
     _ = a n - (L - 1) := by grind

-- 4ª demostración
-- ===============

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
by
  obtain ⟨N, hN⟩ := ha 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  use N
  -- ⊢ ∀ n ≥ N, a n ≥ L - 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ a n ≥ L - 1
  have : -1 < a n - L := (abs_lt.mp (hN n hn)).1
  linarith

-- 5ª demostración
-- ===============

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
by
  obtain ⟨N, hN⟩ := ha 1 (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  refine ⟨N, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ a n ≥ L - 1
  grind

-- 6ª demostración
-- ===============

example
  (ha : LimSuc a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 :=
let ⟨N, hN⟩ := ha 1 (by grind)
⟨N, fun n hn => by grind⟩

-- Lemas usados
-- ============

variable (x y z : ℝ)
#check (abs_lt : |x| < y ↔ -y < x ∧ x < y)
#check (add_lt_add_iff_right x : y + x < z + x ↔ y < z)
#check (ge_iff_le : x ≥ y ↔ y ≤ x)
#check (le_of_lt : x < y → x ≤ y)
#check (neg_le_iff_add_nonneg : -x ≤ y ↔ 0 ≤ y + x)
#check (neg_lt_iff_pos_add : -x < y ↔ 0 < y + x)
#check (one_pos : 0 < 1)
#check (sub_add x y z : x - y + z = x - (y - z))
#check (sub_nonneg : 0 ≤ x - y ↔ y ≤ x)
