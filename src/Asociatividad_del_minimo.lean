-- Asociatividad_del_minimo.lean
-- En ℝ, min(min(a,b),c) = min(a,min(b,c)).
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-septiembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean a, b y c números reales. Demostrar que
--    min (min a b) c = min a (min b c)
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por la propiedad antisimétrica, la igualdad es consecuencia de las
-- siguientes desigualdades
--    min(min(a, b), c) ≤ min(a, min(b, c))                           (1)
--    min(a, min(b, c)) ≤ min(min(a, b), c)                           (2)
--
-- La (1) es consecuencia de las siguientes desigualdades
--    min(min(a, b), c) ≤ a                                          (1a)
--    min(min(a, b), c) ≤ b                                          (1b)
--    min(min(a, b), c) ≤ c                                          (1c)
-- En efecto, de (1b) y (1c) se obtiene
--    min(min(a, b), c) ≤ min(b,c)
-- que, junto con (1a) da (1).
--
-- La (2) es consecuencia de las siguientes desigualdades
--    min(a, min(b, c)) ≤ a                                          (2a)
--    min(a, min(b, c)) ≤ b                                          (2b)
--    min(a, min(b, c)) ≤ c                                          (2c)
-- En efecto, de (2a) y (2b) se obtiene
--    min(a, min(b, c)) ≤ min(a, b)
-- que, junto con (2c) da (2).
--
-- La demostración de (1a) es
--    min(min(a, b), c) ≤ min(a, b) ≤ a
-- La demostración de (1b) es
--    min(min(a, b), c) ≤ min(a, b) ≤ b
-- La demostración de (2b) es
--    min(a, min(b, c)) ≤ min(b, c) ≤ b
-- La demostración de (2c) es
--    min(a, min(b, c)) ≤ min(b, c) ≤ c
-- La (1c) y (2a) son inmediatas.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

variable {a b c : ℝ}

-- Lemas auxiliares
-- ================

lemma aux1a : min (min a b) c ≤ a :=
calc min (min a b) c
     ≤ min a b := by exact min_le_left (min a b) c
   _ ≤ a       := min_le_left a b

lemma aux1b : min (min a b) c ≤ b :=
calc min (min a b) c
     ≤ min a b := by exact min_le_left (min a b) c
   _ ≤ b       := min_le_right a b

lemma aux1c : min (min a b) c ≤ c :=
by exact min_le_right (min a b) c

-- 1ª demostración del lema aux1
lemma aux1 : min (min a b) c ≤ min a (min b c) :=
by
  apply le_min
  { show min (min a b) c ≤ a
    exact aux1a }
  { show min (min a b) c ≤ min b c
    apply le_min
    { show min (min a b) c ≤ b
      exact aux1b }
    { show min (min a b) c ≤ c
      exact aux1c }}

-- 2ª demostración del lema aux1
lemma aux1' : min (min a b) c ≤ min a (min b c) :=
le_min aux1a (le_min aux1b aux1c)

lemma aux2a : min a (min b c) ≤ a :=
by exact min_le_left a (min b c)

lemma aux2b : min a (min b c) ≤ b :=
calc min a (min b c)
     ≤ min b c        := by exact min_le_right a (min b c)
   _ ≤ b              := min_le_left b c

lemma aux2c : min a (min b c) ≤ c :=
calc min a (min b c)
     ≤ min b c        := by exact min_le_right a (min b c)
   _ ≤ c              := min_le_right b c

-- 1ª demostración del lema aux2
lemma aux2 : min a (min b c) ≤ min (min a b) c :=
by
  apply le_min
  { show min a (min b c) ≤ min a b
    apply le_min
    { show min a (min b c) ≤ a
      exact aux2a }
    { show min a (min b c) ≤ b
      exact aux2b }}
  { show min a (min b c) ≤ c
    exact aux2c }

-- 2ª demostración del lema aux2
lemma aux2' : min a (min b c) ≤ min (min a b) c :=
le_min (le_min aux2a aux2b) aux2c

-- 1ª demostración
-- ===============

example :
  min (min a b) c = min a (min b c) :=
by
  apply le_antisymm
  { show min (min a b) c ≤ min a (min b c)
    exact aux1 }
  { show min a (min b c) ≤ min (min a b) c
    exact aux2 }

-- 2ª demostración
-- ===============

example : min (min a b) c = min a (min b c) :=
by
  apply le_antisymm
  { exact aux1 }
  { exact aux2 }

-- 3ª demostración
-- ===============

example : min (min a b) c = min a (min b c) :=
le_antisymm aux1 aux2

-- 4ª demostración
-- ===============

example : min (min a b) c = min a (min b c) :=
min_assoc a b c

-- Lemas usados
-- ============

-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- #check (min_assoc a b c : min (min a b) c = min a (min b c))
-- #check (min_le_left a b : min a b ≤ a)
-- #check (min_le_right a b : min a b ≤ b)
