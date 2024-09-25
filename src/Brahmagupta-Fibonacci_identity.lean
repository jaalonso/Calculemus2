-- Brahmagupta-Fibonacci_identity.lean
-- Brahmagupta–Fibonacci identity.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 25, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Prove the Brahmagupta-Fibonacci identity https://is.gd/9PJ56H
--    (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
-- ---------------------------------------------------------------------

-- Proof in natural language
-- ==========================

-- The proof follows from the following chain of equalities:
--    (a^2 + b^2)(c^2 + d^2) = a^2(c^2 + d^2) + b^2(c^2 + d^2)
--                           = (a^2c^2 + a^2d^2) + b^2(c^2 + d^2)
--                           = (a^2c^2 + a^2d^2) + (b^2c^2 + b^2d^2)
--                           = ((ac)^2 + (bd)^2) + ((ad)^2 + (bc)^2)
--                           = ((ac)^2 - 2acbd + (bd)^2) + ((ad)^2 + 2adbc + (bc)^2)
--                           = (ac - bd)^2 + (ad + bc)^2

-- Proofs with Lean4
-- =================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c d : ℝ)

-- Proof 1
-- =======

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
calc (a^2 + b^2) * (c^2 + d^2)
     = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)
         := right_distrib (a^2) (b^2) (c^2 + d^2)
   _ = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)
         := congr_arg₂ (. + .) (left_distrib (a^2) (c^2) (d^2)) rfl
   _ = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)
         := congr_arg₂ (. + .) rfl (left_distrib (b^2) (c^2) (d^2))
   _ = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)
         := by ring
   _ = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)
         := by ring
   _ = (a*c - b*d)^2 + (a*d + b*c)^2
         := by ring

-- Proof 2
-- =======

example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
by ring

-- Used lemmas
-- ===========

-- variable (f : ℝ → ℝ → ℝ)
-- variable (x x' y y' : ℝ)
-- #check (congr_arg₂ f : x = x' → y = y' → f x y = f x' y')
-- #check (left_distrib a b c : a * (b + c) = a * b + a * c)
-- #check (right_distrib a b c: (a + b) * c = a * c + b * c)
