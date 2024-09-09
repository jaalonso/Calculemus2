-- Sum_of_geometric_progresion.lean
-- Proofs of a+aq+aq²+···+aqⁿ = a(1-qⁿ⁺¹)/(1-q)
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-septiembre-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove that if q ≠ 1, then the sum of the terms of the
-- geometric progression
--    a + aq + aq² + ··· + aqⁿ
-- is
--      a(1 - qⁿ⁺¹)
--    --------------
--        1 - q
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let
--    s(a,q,n) = a + aq + aq² + ··· + aqⁿ
-- We must show that
--    s(a,q,n) = a(1 - qⁿ⁺¹)/(1 - q)
-- or, equivalently, that
--    (1 - q)s(a,q,n) = a(1 - qⁿ⁺¹)
-- We will proceed by induction on n.
--
-- Base case: Let n = 0. Then,
--    (1 - q)s(a,q,n) = (1 - q)s(a, q, 0)
--                    = (1 - q)a
--                    = a(1 - q^(0 + 1))
--                    = a(1 - q^(n + 1))
--
-- Induction step: Let n = m+1 and assume the induction hypothesis
-- (IH)
--    (1 - q)s(a,q,m) = a(1 - q^(m + 1))
-- Then
--    (1 - q)s(a,q,n)
--    = (1 - q)s(a,q,m+1)
--    = (1 - q)(s(a,q,m) + aq^(m + 1))
--    = (1 - q)s(a,q,m) + (1 - q)aq^(m + 1)
--    = a(1 - q^(m + 1)) + (1 - q)aq^(m + 1)   [by IH]
--    = a(1 - q^(m + 1 + 1))
--    = a(1 - q^(n + 1))

-- Proofs with Lean4
-- =================

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (n : ℕ)
variable (a q : ℝ)

set_option pp.fieldNotation false

@[simp]
def sumGP : ℝ → ℝ → ℕ → ℝ
  | a, _, 0     => a
  | a, q, n + 1 => sumGP a q n + (a * q^(n + 1))

-- Proof 1
-- =======

example
  (h : q ≠ 1)
  : sumGP a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))
    calc (1 - q) * sumGP a q 0
         = (1 - q) * a           := by simp only [sumGP]
       _ = a * (1 - q)           := by simp only [mul_comm]
       _ = a * (1 - q ^ 1)       := by simp
       _ = a * (1 - q ^ (0 + 1)) := by simp
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 - q) * sumGP a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumGP a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumGP a q (m + 1)
         = (1 - q) * (sumGP a q m + (a * q^(m + 1)))
           := by simp only [sumGP]
       _ = (1 - q) * sumGP a q m + (1 - q) * (a * q ^ (m + 1))
           := by rw [left_distrib]
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) IH
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf

-- Proof 2
-- =======

example
  (h : q ≠ 1)
  : sumGP a q n = a * (1 - q^(n + 1)) / (1 - q) :=
by
  have h1 : 1 - q ≠ 0 := by exact sub_ne_zero_of_ne (id (Ne.symm h))
  suffices h : (1 - q) * sumGP a q n = a * (1 - q ^ (n + 1))
    from by exact CancelDenoms.cancel_factors_eq_div h h1
  induction n with
  | zero =>
    -- ⊢ (1 - q) * sumGP a q 0 = a * (1 - q ^ (0 + 1))
    simp
    -- ⊢ (1 - q) * a = a * (1 - q)
    ring_nf
  | succ m IH =>
    -- m : ℕ
    -- IH : (1 - q) * sumGP a q m = a * (1 - q ^ (m + 1))
    -- ⊢ (1 - q) * sumGP a q (m + 1) = a * (1 - q ^ (m + 1 + 1))
    calc (1 - q) * sumGP a q (m + 1)
         = (1 - q) * (sumGP a q m + (a * q ^ (m + 1)))
           := rfl
       _ = (1 - q) * sumGP a q m + (1 - q) * (a * q ^ (m + 1))
           := by ring_nf
       _ = a * (1 - q ^ (m + 1)) + (1 - q) * (a * q ^ (m + 1))
           := congrArg  (. + (1 - q) * (a * q ^ (m + 1))) IH
       _ = a * (1 - q ^ (m + 1 + 1))
           := by ring_nf
