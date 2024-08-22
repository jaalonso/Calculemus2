-- El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.lean
-- El punto de acumulación de las sucesiones convergente es su límite.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción f tal que f(n) = 2*n.
--
-- En Lean4, se puede definir que f es una función de extracción por
--    def extraccion (f : ℕ → ℕ) :=
--      ∀ n m, n < m → f n < f m
-- que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
-- que u es convergente por
--    def convergente (u : ℕ → ℝ) :=
--      ∃ a, limite u a
-- que a es un punto de acumulación de u por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ f, extraccion f ∧ limite (u ∘ f) a
--
-- Demostrar que si u es una sucesión convergente y a es un punto de
-- acumulación de u, entonces a es un límite de u.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- En la demostración usaremos los siguientes lemas demostrados en
-- ejercicios anteriores:
-- + Lema 1: El límite de una sucesión es único.
-- + Lema 2: Las subsucesiones de las sucesiones convergentes tienen el
--   mismo límite que la sucesión.
--
-- Puesto que a es un punto de acumulación de u, existe una función de
-- extracción f tal que
--    a es límite de (u ∘ f)                                         (1)
--
-- Por otro lado, por ser u convergente, existe un b tal que
--    b es límite de u                                               (2)
-- Por el Lema 2,
--    b es límite de (u ∘ f)                                         (3)
--
-- Por el Lema 1, (1) y (3)
--   a = b                                                           (4)
-- Por (2) y (4)
--   a es límite de u.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}

def extraccion (f : ℕ → ℕ) :=
  ∀ n m, n < m → f n < f m

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ f, extraccion f ∧ limite (u ∘ f) a

-- Usaremos los siguientes lemas demostrados en ejercicios anteriores.

lemma unicidad_limite_aux
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
by
  by_contra h
  -- h : ¬b ≤ a
  -- ⊢ False
  let ε := b - a
  cases' ha (ε/2) (by linarith) with A hA
  -- A : ℕ
  -- hA : ∀ (n : ℕ), n ≥ A → |u n - a| < ε / 2
  cases' hb (ε/2) (by linarith) with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), n ≥ B → |u n - b| < ε / 2
  let N := max A B
  have hAN : A ≤ N := le_max_left A B
  have hBN : B ≤ N := le_max_right A B
  specialize hA N hAN
  -- hA : |u N - a| < ε / 2
  specialize hB N hBN
  -- hB : |u N - b| < ε / 2
  rw [abs_lt] at hA hB
  -- hA : -(ε / 2) < u N - a ∧ u N - a < ε / 2
  -- hB : -(ε / 2) < u N - b ∧ u N - b < ε / 2
  linarith

lemma unicidad_limite
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (unicidad_limite_aux hb ha)
            (unicidad_limite_aux ha hb)

lemma limite_subsucesion_aux
  (h : extraccion f)
  : ∀ n, n ≤ f n :=
by
  intro n
  induction' n with m HI
  . exact Nat.zero_le (f 0)
  . apply Nat.succ_le_of_lt
    calc m ≤ f m        := HI
         _ < f (succ m) := h m (m+1) (lt_add_one m)

lemma limite_subsucesion
  {f : ℕ → ℕ}
  {a : ℝ}
  (h : limite u a)
  (hf : extraccion f)
  : limite (u ∘ f) a :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  cases' h ε hε with N hN
  -- N : ℕ
  -- hN : ∀ (k : ℕ), k ≥ N → |u k - a| < ε
  use N
  -- ⊢ ∀ (k : ℕ), k ≥ N → |v k - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  have h1 : f n ≥ N := calc
    f n ≥ n := by exact limite_subsucesion_aux hf n
      _ ≥ N := hn
  calc |(u ∘ f ) n  - a| = |u (f n) - a| := by exact rfl
                       _ < ε             := hN (f n) h1


-- 1ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  rcases ha with ⟨f, hf₁, hf₂⟩
  -- f : ℕ → ℕ
  -- hf₁ : extraccion f
  -- hf₂ : limite (u ∘ f) a
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  have hf₃ : limite (u ∘ f) b := limite_subsucesion hb hf₁
  have h : a = b := unicidad_limite hf₂ hf₃
  rwa [h]

-- 2ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  unfold convergente at hu
  -- hu : ∃ a, limite u a
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  unfold punto_acumulacion at ha
  -- ha : ∃ f, extraccion f ∧ limite (u ∘ f) a
  rcases ha with ⟨f, hf₁, hf₂⟩
  -- f : ℕ → ℕ
  -- hf₁ : extraccion f
  -- hf₂ : limite (u ∘ f) a
  have hf₃ : limite (u ∘ f) b := limite_subsucesion hb hf₁
  exact unicidad_limite hf₂ hf₃

-- 3ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  rcases ha with ⟨f, hf₁, hf₂⟩
  -- f : ℕ → ℕ
  -- hf₁ : extraccion f
  -- hf₂ : limite (u ∘ f) a
  apply unicidad_limite hf₂ _
  -- ⊢ limite (u ∘ f) b
  exact limite_subsucesion hb hf₁

-- 4ª demostración
-- ===============

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
by
  cases' hu with b hb
  -- b : ℝ
  -- hb : limite u b
  convert hb
  -- ⊢ a = b
  rcases ha with ⟨f, hf₁, hf₂⟩
  -- f : ℕ → ℕ
  -- hf₁ : extraccion f
  -- hf₂ : limite (u ∘ f) a
  exact unicidad_limite hf₂ (limite_subsucesion hb hf₁)

-- Lemas usados
-- ============

-- variable (b : ℝ)
-- variable (m n : ℕ)
-- #check (Nat.succ_le_of_lt : n < m → succ n ≤ m)
-- #check (Nat.zero_le n : 0 ≤ n)
-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (lt_add_one n : n < n + 1)
