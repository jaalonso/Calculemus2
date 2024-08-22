-- Minimo_de_suma.lean
-- En ℝ, min(a,b)+c = min(a+c,b+c).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a, b y c números reales. Demostrar que
--    min a b + c = min (a + c) (b + c)
-- ----------------------------------------------------------------------

-- Demostraciones en lenguaje natural (LN)
-- =======================================

-- 1ª demostración en LN
-- =====================

-- Aplicando la propiedad antisimétrica a las siguientes desigualdades
--    min(a, b) + c ≤ min(a + c, b + c)                               (1)
--    min(a + c, b + c) ≤ min(a, b) + c                               (2)
--
-- Para demostrar (1) basta demostrar que se verifican las siguientes
-- desigualdades
--    min(a, b) + c ≤ a + c                                          (1a)
--    min(a, b) + c ≤ b + c                                          (1b)
-- que se tienen porque se verifican las siguientes desigualdades
--    min(a, b) ≤ a
--    min(a, b) ≤ b
--
-- Para demostrar (2) basta demostrar que se verifica
--    min(a + c, b + c) - c ≤ min(a, b)
-- que se demuestra usando (1); en efecto,
--    min(a + c, b + c) - c ≤ min(a + c - c, b + c - c)    [por (1)]
--                          = min(a, b)

-- 2ª demostración en LN
-- =====================

-- Por casos según a ≤ b.
--
-- 1º caso: Supongamos que a ≤ b. Entonces,
--    min(a, b) + c = a + c
--                  = min(a + c, b + c)
--
-- 2º caso: Supongamos que a ≰ b. Entonces,
--    min(a, b) + c = b + c
--                  = min(a + c, b + c)

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a b c : ℝ}

-- En las demostraciones se usarán los siguientes lemas auxiliares
--    aux1 : min a b + c ≤ min (a + c) (b + c)
--    aux2 : min (a + c) (b + c) ≤ min a b + c
-- cuyas demostraciones se exponen a continuación.

-- 1ª demostración de aux1
lemma aux1 :
  min a b + c ≤ min (a + c) (b + c) :=
by
  have h1 : min a b ≤ a :=
    min_le_left a b
  have h2 : min a b + c ≤ a + c :=
    add_le_add_right h1 c
  have h3 : min a b  ≤ b :=
    min_le_right a b
  have h4 : min a b + c ≤ b + c :=
    add_le_add_right h3 c
  show min a b + c ≤ min (a + c) (b + c)
  exact le_min h2 h4

-- 2ª demostración de aux1
example :
  min a b + c ≤ min (a + c) (b + c) :=
by
  apply le_min
  { apply add_le_add_right
    exact min_le_left a b }
  { apply add_le_add_right
    exact min_le_right a b }

-- 3ª demostración de aux1
example :
  min a b + c ≤ min (a + c) (b + c) :=
le_min (add_le_add_right (min_le_left a b) c)
       (add_le_add_right (min_le_right a b) c)

-- 1ª demostración de aux2
lemma aux2 :
  min (a + c) (b + c) ≤ min a b + c :=
by
  have h1 : min (a + c) (b + c) + -c ≤ min a b
  { calc min (a + c) (b + c) + -c
         ≤ min (a + c + -c) (b + c + -c) := aux1
       _ = min a b                       := by ring_nf }
  show min (a + c) (b + c) ≤ min a b + c
  exact add_neg_le_iff_le_add.mp h1

-- 1ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  have h1 : min a b + c ≤ min (a + c) (b + c) := aux1
  have h2 : min (a + c) (b + c) ≤ min a b + c := aux2
  show min a b + c = min (a + c) (b + c)
  exact le_antisymm h1 h2

-- 2ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  apply le_antisymm
  { show min a b + c ≤ min (a + c) (b + c)
    exact aux1 }
  { show min (a + c) (b + c) ≤ min a b + c
    exact aux2 }

-- 3ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
by
  apply le_antisymm
  { exact aux1 }
  { exact aux2 }

-- 4ª demostración del ejercicio
example :
  min a b + c = min (a + c) (b + c) :=
le_antisymm aux1 aux2

-- 5ª demostración del ejercicio
example : min a b + c = min (a + c) (b + c) :=
by
  by_cases h : a ≤ b
  { have h1 : a + c ≤ b + c := add_le_add_right h c
    calc min a b + c = a + c               := by simp [min_eq_left h]
                   _ = min (a + c) (b + c) := by simp [min_eq_left h1]}
  { have h2: b ≤ a := le_of_not_le h
    have h3 : b + c ≤ a + c := add_le_add_right h2 c
    calc min a b + c = b + c               := by simp [min_eq_right h2]
                   _ = min (a + c) (b + c) := by simp [min_eq_right h3]}

-- 6ª demostración del ejercicio
example : min a b + c = min (a + c) (b + c) :=
(min_add_add_right a b c).symm

-- Lemas usados
-- ============

-- #check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
-- #check (add_neg_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b)
-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- #check (min_add_add_right a b c : min (a + c) (b + c) = min a b + c)
-- #check (min_eq_left : a ≤ b → min a b = a)
-- #check (min_eq_right : b ≤ a → min a b = b)
-- #check (min_le_left a b : min a b ≤ a)
-- #check (min_le_right a b : min a b ≤ b)
