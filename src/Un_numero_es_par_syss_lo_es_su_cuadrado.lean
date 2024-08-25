-- Un_numero_es_par_syss_lo_es_su_cuadrado.lean
-- Un número es par si y solo si lo es su cuadrado
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que un número es par si y solo si lo es su cuadrado.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea n ∈ ℤ. Tenemos que demostrar que n² es par si y solo si n es
-- par. Lo haremos probando las dos implicaciones.
--
-- (⟹) Lo demostraremos por contraposición. Para ello, supongamos que n
-- no es par. Entonces, existe un k ∈ Z tal que
--    n = 2k+1                                                       (1)
-- Luego,
--    n² = (2k+1)²          [por (1)]
--       = 4k²+4k+1
--       = 2(2k(k+1))+1
-- Por tanto, n² es impar.
--
-- (⟸) Supongamos que n es par. Entonces, existe un k ∈ ℤ tal que
--    n = 2k                                                         (2)
-- Luego,
--    n² = (2k)²          [por (2)]
--        = 2(2k²)
-- Por tanto, n² es par.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

open Int

variable (n : ℤ)

-- 1ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    intro h
    -- h : ¬Even n
    -- ⊢ ¬Even (n ^ 2)
    rw [not_even_iff_odd] at *
    -- h : Odd n
    -- ⊢ Odd (n ^ 2)
    cases' h with k hk
    -- k : ℤ
    -- hk : n = 2 * k + 1
    use 2*k*(k+1)
    -- ⊢ n ^ 2 = 2 * (2 * k * (k + 1)) + 1
    calc n^2
         = (2*k+1)^2       := by rw [hk]
       _ = 4*k^2+4*k+1     := by ring
       _ = 2*(2*k*(k+1))+1 := by ring
  . -- ⊢ Even n → Even (n ^ 2)
    intro h
    -- h : Even n
    -- ⊢ Even (n ^ 2)
    cases' h with k hk
    -- k : ℤ
    -- hk : n = k + k
    use 2*k^2
    -- ⊢ n ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    calc n^2
         = (k + k)^2     := by rw [hk]
       _ = 2*k^2 + 2*k^2 := by ring

-- 2ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    rw [not_even_iff_odd]
    -- ⊢ Odd n → ¬Even (n ^ 2)
    rw [not_even_iff_odd]
    -- ⊢ Odd n → Odd (n ^ 2)
    unfold Odd
    -- ⊢ (∃ k, n = 2 * k + 1) → ∃ k, n ^ 2 = 2 * k + 1
    intro h
    -- h : ∃ k, n = 2 * k + 1
    -- ⊢ ∃ k, n ^ 2 = 2 * k + 1
    cases' h with k hk
    -- k : ℤ
    -- hk : n = 2 * k + 1
    use 2*k*(k+1)
    -- ⊢ n ^ 2 = 2 * (2 * k * (k + 1)) + 1
    rw [hk]
    -- ⊢ (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1
    ring
  . -- ⊢ Even n → Even (n ^ 2)
    unfold Even
    -- ⊢ (∃ r, n = r + r) → ∃ r, n ^ 2 = r + r
    intro h
    -- h : ∃ r, n = r + r
    -- ⊢ ∃ r, n ^ 2 = r + r
    cases' h with k hk
    -- k : ℤ
    -- hk : n = k + k
    use 2*k^2
    -- ⊢ n ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    rw [hk]
    -- ⊢ (k + k) ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    ring

-- 3ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    rw [not_even_iff_odd]
    -- ⊢ Odd n → ¬Even (n ^ 2)
    rw [not_even_iff_odd]
    -- ⊢ Odd n → Odd (n ^ 2)
    rintro ⟨k, rfl⟩
    -- k : ℤ
    -- ⊢ Odd ((2 * k + 1) ^ 2)
    use 2*k*(k+1)
    -- ⊢ (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1
    ring
  . -- ⊢ Even n → Even (n ^ 2)
    rintro ⟨k, rfl⟩
    -- k : ℤ
    -- ⊢ Even ((k + k) ^ 2)
    use 2*k^2
    -- ⊢ (k + k) ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    ring

-- 4ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
calc Even (n^2)
     ↔ Even (n * n)      := iff_of_eq (congrArg Even (sq n))
   _ ↔ (Even n ∨ Even n) := even_mul
   _ ↔ Even n            := by rw [or_self_iff]

-- 5ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
calc Even (n^2)
     ↔ Even (n * n)      := by ring_nf
   _ ↔ (Even n ∨ Even n) := even_mul
   _ ↔ Even n            := by simp only [or_self]

-- Lemas usados
-- ============

-- variable (a b : Prop)
-- variable (m : ℤ)
-- #check (even_mul : Even (m * n) ↔ Even m ∨ Even n)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (not_even_iff_odd : Odd n ↔ ¬Even n)
-- #check (or_self_iff a : a ∨ a ↔ a)
