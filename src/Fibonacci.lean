-- Fibonacci.lean
-- Equivalence of definitions of the Fibonacci function.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, August 29, 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- In Lean4, the Fibonacci function can be defined as
--    def fibonacci : Nat → Nat
--      | 0     => 0
--      | 1     => 1
--      | n + 2 => fibonacci n + fibonacci (n+1)
--
-- Another more efficient definition is
--    def fib (n : Nat) : Nat :=
--      (loop n).1
--    where
--      loop : Nat → Nat × Nat
--        | 0   => (0, 1)
--        | n + 1 =>
--          let p := loop n
--          (p.2, p.1 + p.2)
--
-- Prove that both definitions are equivalent; that is,
--    fibonacci = fib
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- From the definition of the mirror function, we have the following lemma
--    fib_suma : fib (n + 2) = fib n + fib (n + 1)
--
-- We need to prove that, for all n ∈ ℕ,
--    fibonacci n = fib n
-- We will prove this by induction on n
--
-- Case 1: Suppose that n = 0. Then,
--    fibonacci n = fibonacci 0
--                = 1
-- and
--    fib n = fib 0
--          = (loop 0).1
--          = (0, 1).1
--          = 1
-- Therefore,
--     fibonacci n = fib n
--
-- Case 2: Suppose that n = 1. Then,
--    fibonacci n = 1
-- and
--    fib 1 = (loop 1).1
--          = (p.2, p.1 + p.2).1
--            donde p = loop 0
--          = ((0, 1).2, (0, 1).1 + (0, 1).2).1
--          = (1, 0 + 1).1
--          = 1
-- Therefore,
--     fibonacci n = fib n
--
-- Case 3: Suppose that n = m + 2 and that the induction hypotheses hold,
--    ih1 : fibonacci n = fib n
--    ih2 : fibonacci (n + 1) = fib (n + 1)
-- Then,
--    fibonacci n
--    = fibonacci (m + 2)
--    = fibonacci m + fibonacci (m + 1)
--    = fib m + fib (m + 1)                [por ih1, ih2]
--    = fib (m + 2)                        [por fib_suma]
--    = fib n

-- Proof with Lean4
-- ================

open Nat

set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

-- Auxiliary lemma
-- ===============

theorem fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1) :=
by rfl

-- Proof 1
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    rw [fib_suma]
    -- ⊢ fibonacci (succ (succ n)) = fib n + fib (n + 1)
    rw [fibonacci]
    -- ⊢ fibonacci n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [ih1]
    -- ⊢ fib n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [ih2]

-- Proof 2
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    calc fibonacci (succ (succ n))
         = fibonacci n + fibonacci (n + 1) := by rw [fibonacci]
       _ = fib n + fib (n + 1)             := by rw [ih1, ih2]
       _ = fib (succ (succ n))             := by rw [fib_suma]

-- Proof 3
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    simp [ih1, ih2, fibonacci, fib_suma]
