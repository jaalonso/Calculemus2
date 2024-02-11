-- Unicidad_del_limite_de_las_sucesiones_convergentes.lean
-- Unicidad del límite de las sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 12 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--    λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- donde se usa la notación |x| para el valor absoluto de x
--    notation `|`x`|` := abs x
--
-- Demostrar que cada sucesión tiene como máximo un límite.
-- ---------------------------------------------------------------------

import data.real.basic

variables {u : ℕ → ℝ}
variables {a b : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

lemma aux
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
begin
  by_contra h,
  set ε := b - a with hε,
  cases ha (ε/2) (by linarith) with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (aux hb ha) (aux ha hb)

-- 2ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  by_contra h,
  wlog hab : a < b,
  { have : a < b ∨ a = b ∨ b < a := lt_trichotomy a b,
    tauto },
  set ε := b - a with hε,
  specialize ha (ε/2),
  have hε2 : ε/2 > 0 := by linarith,
  specialize ha hε2,
  cases ha with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end

-- 3ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  by_contra h,
  wlog hab : a < b,
  { have : a < b ∨ a = b ∨ b < a := lt_trichotomy a b,
    tauto },
  set ε := b - a with hε,
  cases ha (ε/2) (by linarith) with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end
