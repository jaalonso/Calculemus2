-- Reto_1_Soluciones.lean
-- Soluciones de reto 1 (del 10 de mayo de 2026)
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión a₀,a₁,a₂,... se puede representar mediante una
-- función  (a : ℕ → ℝ) de forma que a(n) es aₙ.
--
-- Se define que L es el límite de la sucesión a, por
--
-- def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--   ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
--
-- Demostrar que si para todo n, aₙ=1/n, entonces la sucesión a converge
-- a 0.
--
-- Para ello, completar la siguiente teoría de Lean 4:
--
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Tactic
--
-- variable (a : ℕ → ℝ)
--
-- def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--   ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
--
-- example
--   (ha : ∀ n, a n = 1 / n)
--   : LimSuc a 0 :=
-- by sorry
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Por la propiedad arquimediana, existe N ∈ ℕ
-- tal que
--    1 / ε < N                                                      (1)
-- Veamos que, para todo n ≥ N, |a(n) - 0| < ε. En efecto, sea
--    n ≥ N                                                          (2)
-- Entonces,
--    |a(n) - 0| = |1/n - 0|
--               = 1/n
--               ≤ 1/N          [por (2)]
--               < ε            [por (1)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª solución (Esteban Martínez Vañó)
-- ===================================

namespace Solucion1

-- Demostración de la propiedad arquimediana
theorem arquim : ∀ (x y: ℝ), x > 0 → ∃ n: ℕ, n*x>y := by
  intro x y xpos
  let A := {z: ℝ | ∃ (n: ℕ), z = n * x}
  by_contra! C
  have Aacotado : BddAbove A := by
    apply bddAbove_def.mpr
    use y
    intro z zinA
    rcases zinA with ⟨m, hm⟩
    rw [hm]
    exact C m
  have Asup : ∃ a, IsLUB A a := by
    apply Real.exists_isLUB _ Aacotado
    rw [Set.nonempty_def]
    use x
    rw [Set.mem_setOf_eq]
    use 1
    rw [Nat.cast_one, one_mul]
  rcases Asup with ⟨a, ha⟩
  rw [IsLUB, IsLeast, mem_upperBounds, mem_lowerBounds] at ha
  have hdes : ∃ (m: ℕ), a < (m + 1) * x := by
    have nocotasup : ¬ (a - x ∈ upperBounds A) := by
      by_contra! C
      linarith [ha.2 (a-x) C]
    rw [mem_upperBounds, not_forall] at nocotasup
    simp only [Classical.not_imp, not_le] at nocotasup
    rcases nocotasup with ⟨z, hz⟩
    rcases hz.1 with ⟨m, hm⟩
    use m
    rw [right_distrib, one_mul, ← hm]
    exact sub_lt_iff_lt_add.mp hz.2
  rcases hdes with ⟨m, hm⟩
  have hmem : (m + 1) * x ∈ A := by
    rw [Set.mem_setOf_eq]
    use m + 1
    rw[Nat.cast_add,  Nat.cast_one]
  exact lt_irrefl a (lt_of_lt_of_le hm (ha.1 ((m + 1) * x) hmem))

-- Corolario de la propiedad arquimediana
theorem arquim' : ∀ x > 0, ∃ (n: ℕ), (n > 0 ∧ (1:ℝ)/n < x) := by
  intro x xpos
  rcases arquim x 1 xpos with ⟨n, hn⟩
  use n
  have npos : n > 0 := by
    by_contra! C
    rw[nonpos_iff_eq_zero] at C
    rw [C, Nat.cast_zero, zero_mul, gt_iff_lt] at hn
    exact lt_irrefl 0 (lt_trans zero_lt_one hn)
  constructor
  · exact npos
  · rw [gt_iff_lt] at *
    rw [div_lt_iff₀ _, mul_comm]
    · exact hn
    · exact Nat.cast_pos.mpr npos

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro eps epos
  rcases arquim' eps epos with ⟨N, hN⟩
  use N
  intro n ngeqN
  rw [ha n, sub_zero, abs_div, abs_one, Nat.abs_cast]
  have divLe : 1/(n: ℝ) ≤ 1/(N: ℝ) := by
    apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hN.1) (Nat.cast_le.mpr ngeqN)
  apply lt_of_le_of_lt divLe hN.2

end Solucion1

-- 2ª solución (refactorización de la 1ª)
-- ======================================

namespace Solucion2

variable (x y : ℝ)

-- Demostración de la propiedad arquimediana
theorem arquim
  (hx : x > 0)
  : ∃ n : ℕ, y < n * x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  -- n : ℕ
  -- hn : y / x < ↑n
  use n
  -- ⊢ y < ↑n * x
  exact (mul_inv_lt_iff₀ hx).mp hn

-- Corolario de la propiedad arquimediana
theorem arquim'
  (hx :   x > 0)
  : ∃ n : ℕ, n > (0 : ℝ) ∧ (1 : ℝ) / n < x := by
  rcases arquim x 1 hx with ⟨n, hn⟩
  -- n : ℕ
  -- hn : 1 < ↑n * x
  use n
  -- ⊢ ↑n > 0 ∧ 1 / ↑n < x
  constructor
  · -- ⊢ ⊢ ↑n > 0
    nlinarith [hx, hn]
  · -- ⊢ 1 / ↑n < x
    apply (div_lt_iff₀ (by nlinarith)).mpr
    -- ⊢ 1 < x * ↑n
    rw [mul_comm]
    -- ⊢ 1 < ↑n * x
    exact hn

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε εpos
  -- ε : ℝ
  -- εpos : eps > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < eps
  rcases arquim' ε εpos with ⟨N, hN⟩
  -- N : ℕ
  -- hN : N > 0 ∧ 1 / N < ε
  use N
  -- ⊢ ∀ n ≥ N, |a n - 0| < ε
  intro n ngeqN
  -- n : ℕ
  -- ngeqN : n ≥ N
  -- ⊢ |a n - 0| < ε
  rw [ha n, sub_zero]
  -- ⊢ |1 / ↑n| < ε
  have hnpos : 0 < (n : ℝ) := by
    have : (N : ℝ) ≤ n := Nat.cast_le.mpr ngeqN
    linarith [hN.1, this]
  rw [abs_of_pos (by positivity)]
  -- ⊢ 1 / ↑n < ε
  exact lt_of_le_of_lt (one_div_le_one_div_of_le hN.1 (Nat.cast_le.mpr ngeqN)) hN.2

end Solucion2

-- 3ª solución (Anónima)
-- =====================

namespace Solucion3

example (ha : ∀ n, a n = 1 / n) : LimSuc a 0 := by
  intro ε hε
  -- Dado ε > 0, existe un natural N estrictamente mayor que 1/ε
  rcases exists_nat_gt (1 / ε) with ⟨N, hN⟩
  use N
  intro n hn
  -- Como N > 1/ε > 0, deducimos N > 0 y, puesto que n ≥ N, también n > 0
  have hN_pos : (N : ℝ) > 0 := by linarith [hN, show (0 : ℝ) < 1 / ε by positivity]
  have hn_pos : (n : ℝ) > 0 := by
    have : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
    linarith
  calc
    |a n - 0| = |1 / (n : ℝ)| := by rw [ha n]; norm_num
    _ = 1 / (n : ℝ) := by
      rw [abs_of_nonneg]
      positivity
    _ ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast hN_pos
      · exact_mod_cast hn
    _ < ε := by
      -- De N > 1/ε y ε > 0 se sigue ε·N > 1, luego 1/N < ε
      have hN_lt : (N : ℝ) > 1 / ε := by exact_mod_cast hN
      have h1 : ε * (N : ℝ) > 1 := by
        have h2 : ε * (N : ℝ) > ε * (1 / ε) := by
          apply mul_lt_mul_of_pos_left
          · exact_mod_cast hN_lt
          · exact hε
        have h3 : ε * (1 / ε) = 1 := by field_simp
        linarith
      apply (div_lt_iff₀ hN_pos).mpr
      linarith

end Solucion3

-- 4ª solución (refactorización de la 3ª)
-- ======================================

namespace Solucion4

lemma L1
  {ε N : ℝ}
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : N > 0 :=
calc (0 : ℝ) < 1 / ε := by positivity
           _ < N     := hN

lemma L2
  {N n : ℕ}
  (hN_pos : (N : ℝ) > 0)
  (hn : n ≥ N)
  : (n : ℝ) > 0 :=
by
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  -- this : ↑N ≤ ↑n
  linarith

lemma L3
  {n : ℝ}
  (hn : n > 0)
  : |1 / n| = 1 / n :=
by grind

lemma L4
  {ε N n : ℝ}
  (hε : ε > 0)
  (hN : N > 0)
  (hN_lt : 1 / ε < N)
  (hN_le_n : N ≤ n)
  : 1 / n < ε :=
by
  have : 1 / ε < n := by linarith
  -- this : 1 / ε < n
  have hn_pos : n > 0 := by linarith
  exact (one_div_lt hε hn_pos).mp this

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  -- N : ℕ
  -- hN : 1 / ε < ↑N
  refine ⟨N, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |a n - 0| < ε
  have hN_pos : (N : ℝ) > 0 := L1 hε (by exact_mod_cast hN)
  have hn_pos : (n : ℝ) > 0 := L2 hN_pos hn
  calc |a n - 0|
       = |1 / (n : ℝ)| := by rw [ha n, sub_zero]
     _ = 1 / (n : ℝ)   := L3 hn_pos
     _ < ε             := L4 hε hN_pos (by exact_mod_cast hN) (by exact_mod_cast hn)

end Solucion4

-- 5ª solución
-- ===========

namespace Solucion5

variable {ε : ℝ}
variable {N : ℕ}

lemma L1
  {n : ℕ}
  : |1 / (n : ℝ)| = 1 / n :=
by
  apply abs_of_nonneg
  -- ⊢ 0 ≤ 1 / ↑n
  positivity

lemma L2
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 0 < (N : ℝ) :=
by calc
  (0 : ℝ) < 1 / ε := by positivity
  _       < N     := hN

lemma L3
  (hε : ε > 0)
  {n : ℕ}
  (hN : 1 / ε < N)
  (hn : n ≥ N)
  : 1 / (n : ℝ) ≤ 1 / (N : ℝ) :=
by
  apply one_div_le_one_div_of_le
  · -- ⊢ 0 < ↑N
    exact L2 hε hN
  · -- ⊢ ↑N ≤ ↑n
    gcongr

lemma L4
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 1 / (N : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑N
    gcongr
  · -- ⊢ 0 < ε
    gcongr
  · -- ⊢ 0 < ↑N
    exact L2 hε hN

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  have h1 : ∃ (N : ℕ), 1 / ε < N := exists_nat_gt (1 / ε)
  choose N hN using h1
  -- N : ℕ
  -- hN : 1 / ε < ↑N
  use N
  --⊢ ∀ n ≥ N, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |a n - 0| < ε
  calc |a n - 0|
       = |a n|         := by norm_num
     _ = |1 / (n : ℝ)| := by rw [ha]
     _ = 1 / n         := L1
     _ ≤ 1 / N         := L3 hε hN hn
     _ < ε             := L4 hε hN

end Solucion5

-- 6ª solución
-- ===========

namespace Solucion6

variable {ε : ℝ}
variable {N : ℕ}

lemma L0
  {n : ℕ}
  : 0 ≤ 1 / (n : ℝ) :=
by
  -- ⊢ 0 ≤ 1 / ↑n
  apply div_nonneg
  · -- ⊢ 0 ≤ 1
    exact zero_le_one
  · -- ⊢ 0 ≤ ↑n
    exact Nat.cast_nonneg n

lemma L1
  {n : ℕ}
  : |1 / (n : ℝ)| = 1 / n :=
by
  apply abs_of_nonneg
  -- ⊢ 0 ≤ 1 / ↑n
  exact L0

lemma L2
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 0 < (N : ℝ) :=
by calc
  (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  _       < N     := hN

lemma L3
  (hε : ε > 0)
  {n : ℕ}
  (hN : 1 / ε < N)
  (hn : n ≥ N)
  : 1 / (n : ℝ) ≤ 1 / (N : ℝ) :=
by
  apply one_div_le_one_div_of_le
  · -- ⊢ 0 < ↑N
    exact L2 hε hN
  · -- ⊢ ↑N ≤ ↑n
    exact Nat.cast_le.mpr hn

lemma L4
  (hε : ε > 0)
  (hN : 1 / ε < N)
  : 1 / (N : ℝ) < ε :=
by
  apply (one_div_lt _ _).mp
  · -- ⊢ 1 / ε < ↑N
    exact RCLike.ofReal_lt_ofReal.mp hN
  · -- ⊢ 0 < ε
    exact RCLike.ofReal_pos.mp hε
  · -- ⊢ 0 < ↑N
    exact L2 hε hN

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  have h1 : ∃ (N : ℕ), 1 / ε < N := exists_nat_gt (1 / ε)
  choose N hN using h1
  -- N : ℕ
  -- hN : 1 / ε < ↑N
  use N
  -- ⊢ ∀ n ≥ N, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |a n - 0| < ε
  calc |a n - 0|
       = |a n|         := by simp [sub_zero]
     _ = |1 / (n : ℝ)| := by rw [ha]
     _ = 1 / n         := L1
     _ ≤ 1 / N         := L3 hε hN hn
     _ < ε             := L4 hε hN

end Solucion6

-- 7ª solución (xPrivo)
-- ====================

namespace Solucion7

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  -- N : ℕ
  -- hN : 1 / (↑N + 1) < ε
  use N + 1
  -- ⊢ ∀ n ≥ N + 1, |a n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N + 1
  -- ⊢ |a n - 0| < ε
  rw [ha n, sub_zero]
  -- ⊢ |1 / ↑n| < ε
  have hn' : (N + 1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hle : (1 : ℝ) / n ≤ 1 / (N + 1 : ℝ) := one_div_le_one_div_of_le hpos hn'
  have habs : |(1 : ℝ) / n| = (1 : ℝ) / n := by
    rw [abs_of_nonneg]
    -- ⊢ 0 ≤ 1 / ↑n
    positivity
  rw [habs]
  -- ⊢ 1 / ↑n < ε
  exact lt_of_le_of_lt hle hN

end Solucion7

-- 8ª solución (refactorización de la 5ª)
-- ======================================

namespace Solucion8

lemma L1
  {N n : ℕ}
  (h : N + 1 ≤ n)
  : (1 : ℝ) / n ≤ 1 / (N + 1 : ℝ) :=
by
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have h' : (N + 1 : ℝ) ≤ n := by exact_mod_cast h
  exact one_div_le_one_div_of_le hpos h'

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N + 1, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N + 1
  -- ⊢ |a n - 0| < ε
  rw [ha n, sub_zero, abs_of_nonneg]
  · -- ⊢ 1 / ↑n < ε
    exact lt_of_le_of_lt (L1 hn) hN
  · -- ⊢ 0 ≤ 1 / ↑n
    positivity

end Solucion8

-- 9ª solución (refactorización de la 5ª)
-- ======================================

namespace Solucion9

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  -- N : ℕ
  -- hN : 1 / (↑N + 1) < ε
  refine ⟨N + 1, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N + 1
  -- ⊢ |a n - 0| < ε
  rw [ha n, sub_zero, abs_of_nonneg]
  · -- ⊢ 1 / ↑n < ε
    have h' : (N + 1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (N + 1 : ℝ) := by positivity
    exact lt_of_le_of_lt (one_div_le_one_div_of_le hpos h') hN
  · -- ⊢ 0 ≤ 1 / ↑n
    positivity

end Solucion9

-- 10ª solución (Aristotle)
-- =======================

namespace Solucion10

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |a n - 0| < ε
  refine ⟨⌊ε⁻¹⌋₊ + 1, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ ⌊ε⁻¹⌋₊ + 1
  -- ⊢ |a n - 0| < ε
  have h1 : ε⁻¹ < n := Nat.lt_of_floor_lt hn
  have h2 : (↑n)⁻¹ < ε := inv_lt_of_inv_lt₀ hε h1
  simpa [ha, abs_inv] using h2

end Solucion10

-- 11ª solución (refactorización de la 8ª)
-- ======================================

namespace Solucion11

example
  (ha : ∀ n, a n = 1 / n)
  : LimSuc a 0 :=
  fun ε hε => ⟨⌊ε⁻¹⌋₊ + 1, fun n hn => by simpa [abs_inv, ha] using inv_lt_of_inv_lt₀ hε <| Nat.lt_of_floor_lt hn⟩

end Solucion11

-- Comentarios
-- ===========

-- + Las soluciones 1 y 2 demuestran explícitamente la propiedad
--   arquimediana desde cero. Son muy completas, pero extensas
--   (especialmente la 1).
-- + Las soluciones 3 a 6 usan exists_nat_gt.
-- + Las soluciones 7 a 9 usan exists_nat_one_div_lt que es más directa
--   para este problema. La 9 es muy clara, concisa y bien estructurada.
-- + Las soluciones 10 y 11 usan ⌊ε⁻¹⌋₊ (suelo natural de 1/ε) y el lema
--   inv_lt_of_inv_lt₀. La 11 es extremadamente compacta la 11, pero
--   pueden ser crípticas para principiantes.

-- Observaciones sobre estilos
-- ===========================

-- + La solución 11 es la más impresionante técnicamente.
-- + La solución 9 es la más didáctica para estudiantes intermedios
-- + La solución 2 tiene el mejor balance entre rigor y uso de la
--   biblioteca.
-- + La solución 1 es útil para demostrar la propiedad arquimediana.
