-- Cotas_superiores_de_conjuntos.lean
-- Si a es una cota superior de s y a ≤ b, entonces b es una cota superior de s.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una cota superior de s y a ≤ b, entonces b es
-- una cota superior de s.
-- ----------------------------------------------------------------------

import Mathlib.Tactic

variable {α : Type _} [PartialOrder α]
variable (s : Set α)
variable (a b : α)

-- (CotaSupConj s a) afirma que a es una cota superior del conjunto s.
def CotaSupConj (s : Set α) (a : α) :=
  ∀ {x}, x ∈ s → x ≤ a

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que
--    (∀ x) [x ∈ s → x ≤ b]
-- Sea x tal que x ∈ s. Entonces,
--    x ≤ a   [porque a es una cota superior de s]
--      ≤ b
-- Por tanto, x ≤ b.

-- 1ª demostración
example
  (h1 : CotaSupConj s a)
  (h2 : a ≤ b)
  : CotaSupConj s b :=
by
  intro x (xs : x ∈ s)
  have h3 : x ≤ a := h1 xs
  show x ≤ b
  exact le_trans h3 h2

-- 2ª demostración
example
  (h1 : CotaSupConj s a)
  (h2 : a ≤ b)
  : CotaSupConj s b :=
by
  intro x (xs : x ∈ s)
  calc x ≤ a := h1 xs
       _ ≤ b := h2

-- Lemas usados
-- ============

-- variable (c : α)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
