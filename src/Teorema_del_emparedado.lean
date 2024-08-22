-- Teorema_del_emparedado.lean
-- Teorema del emparedado
-- José A. Alonso Jiménez
-- Sevilla, 19 de febrero de 2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--      fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε
--
-- Demostrar que si para todo n, u(n) ≤ v(n) ≤ w(n) y u(n) tiene el
-- mismo límite que w(n), entonces v(n) también tiene dicho límite.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada ε > 0, existe un N ∈ ℕ tal que
--    (∀ n ≥ N)[|v(n) - a| ≤ ε]                                       (1)
--
-- Puesto que el límite de u es a, existe un U ∈ ℕ tal que
--    (∀ n ≥ U)[|u(n) - a| ≤ ε]                                       (2)
-- y, puesto que el límite de w es a, existe un W ∈ ℕ tal que
--    (∀ n ≥ W)[|w(n) - a| ≤ ε]                                       (3)
-- Sea N = máx(U, W). Veamos que se verifica (1). Para ello, sea
-- n ≥ N. Entonces, n ≥ U y n ≥ W. Por (2) y (3), se tiene que
--     |u(n) - a| ≤ ε                                                 (4)
--     |w(n) - a| ≤ ε                                                 (5)
-- Para demostrar que
--     |v(n) - a| ≤ ε
-- basta demostrar las siguientes desigualdades
--     -ε ≤ v(n) - a                                                  (6)
--      v(n) - a ≤ ε                                                  (7)
-- La demostración de (6) es
--    -ε ≤ u(n) - a    [por (4)]
--       ≤ v(n) - a    [por hipótesis]
-- La demostración de (7) es
--    v(n) - a ≤ w(n) - a    [por hipótesis]
--             ≤ ε           [por (5)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (u v w : ℕ → ℝ)
variable (a : ℝ)

def limite : (ℕ → ℝ) → ℝ → Prop :=
  fun u c ↦ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- Nota. En la demostración se usará el siguiente lema:
lemma max_ge_iff
  {p q r : ℕ}
  : r ≥ max p q ↔ r ≥ p ∧ r ≥ q :=
  max_le_iff

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  -- ⊢ |v n - a| ≤ ε
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n hn.1
  -- hU : |u n - a| ≤ ε
  specialize hW n hn.2
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  clear hn
  rw [abs_le] at *
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor
  . -- ⊢ -ε ≤ v n - a
    calc -ε
         ≤ u n - a := hU.1
       _ ≤ v n - a := by linarith
  . -- ⊢ v n - a ≤ ε
    calc v n - a
         ≤ w n - a := by linarith
       _ ≤ ε       := hW.2

-- 2ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n (by linarith)
  -- hU : |u n - a| ≤ ε
  specialize hW n (by linarith)
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  rw [abs_le] at *
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor
  . -- ⊢ -ε ≤ v n - a
    linarith
  . -- ⊢ v n - a ≤ ε
    linarith

-- 3ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h1 : ∀ n, u n ≤ v n)
  (h2 : ∀ n, v n ≤ w n) :
  limite v a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |v n - a| ≤ ε
  rcases hu ε hε with ⟨U, hU⟩
  -- U : ℕ
  -- hU : ∀ (n : ℕ), n ≥ U → |u n - a| ≤ ε
  clear hu
  rcases hw ε hε with ⟨W, hW⟩
  -- W : ℕ
  -- hW : ∀ (n : ℕ), n ≥ W → |w n - a| ≤ ε
  clear hw hε
  use max U W
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max U W
  -- ⊢ |v n - a| ≤ ε
  rw [max_ge_iff] at hn
  -- hn : n ≥ U ∧ n ≥ W
  specialize hU n (by linarith)
  -- hU : |u n - a| ≤ ε
  specialize hW n (by linarith)
  -- hW : |w n - a| ≤ ε
  specialize h1 n
  -- h1 : u n ≤ v n
  specialize h2 n
  -- h2 : v n ≤ w n
  rw [abs_le] at *
  -- hU : -ε ≤ u n - a ∧ u n - a ≤ ε
  -- hW : -ε ≤ w n - a ∧ w n - a ≤ ε
  -- ⊢ -ε ≤ v n - a ∧ v n - a ≤ ε
  constructor <;> linarith
