---
Título: (a + b) * (a - b) = a^2 - b^2
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a y b son números reales, entonces
<pre lang="text">
   (a + b) * (a - b) = a^2 - b^2
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

example : (a + b) * (a - b) = a^2 - b^2 :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℝ)

-- 1ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by rw [add_mul]
  _ = (a * a - a * b) + b * (a - b)     := by rw [mul_sub]
  _ = (a^2 - a * b) + b * (a - b)       := by rw [← pow_two]
  _ = (a^2 - a * b) + (b * a - b * b)   := by rw [mul_sub]
  _ = (a^2 - a * b) + (b * a - b^2)     := by rw [← pow_two]
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by rw [add_assoc]
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by rw [← add_assoc
                                              (-(a * b)) (b * a) (-b^2)]
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by rw [mul_comm]
  _ = a^2 + (0 + -b^2)                  := by rw [neg_add_self (a * b)]
  _ = (a^2 + 0) + -b^2                  := by rw [← add_assoc]
  _ = a^2 + -b^2                        := by rw [add_zero]
  _ = a^2 - b^2                         := by linarith

-- Comentario. Se han usado los siguientes lemas:
-- + pow_two a : a ^ 2 = a * a
-- + mul_sub a b c : a * (b - c) = a * b - a * c
-- + add_mul a b c : (a + b) * c = a * c + b * c
-- + add_sub a b c : a + (b - c) = a + b - c
-- + sub_sub a b c : a - b - c = a - (b + c)
-- + add_zero a : a + 0 = a

-- 2ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
    = a * (a - b) + b * (a - b)         := by ring
  _ = (a * a - a * b) + b * (a - b)     := by ring
  _ = (a^2 - a * b) + b * (a - b)       := by ring
  _ = (a^2 - a * b) + (b * a - b * b)   := by ring
  _ = (a^2 - a * b) + (b * a - b^2)     := by ring
  _ = (a^2 + -(a * b)) + (b * a - b^2)  := by ring
  _ = a^2 + (-(a * b) + (b * a - b^2))  := by ring
  _ = a^2 + (-(a * b) + (b * a + -b^2)) := by ring
  _ = a^2 + ((-(a * b) + b * a) + -b^2) := by ring
  _ = a^2 + ((-(a * b) + a * b) + -b^2) := by ring
  _ = a^2 + (0 + -b^2)                  := by ring
  _ = (a^2 + 0) + -b^2                  := by ring
  _ = a^2 + -b^2                        := by ring
  _ = a^2 - b^2                         := by ring

-- 3ª demostración
-- ===============

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

-- 4ª demostración (por reescritura usando el lema anterior)
-- =========================================================

-- El lema anterior es
lemma aux : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- La demostración es
example : (a + b) * (a - b) = a^2 - b^2 :=
by
  rw [sub_eq_add_neg]
  rw [aux]
  rw [mul_neg]
  rw [add_assoc (a * a)]
  rw [mul_comm b a]
  rw [neg_add_self]
  rw [add_zero]
  rw [← pow_two]
  rw [mul_neg]
  rw [← pow_two]
  rw [← sub_eq_add_neg]


-- El desarrollo de la demostración es
--    ⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2
-- rw [sub_eq_add_neg]
--    ⊢ (a + b) * (a + -b) = a ^ 2 - b ^ 2
-- rw aux]
--    ⊢ a * a + a * -b + b * a + b * -b = a ^ 2 - b ^ 2
-- rw [mul_neg_eq_neg_mul_symm]
--    ⊢ a * a + -(a * b) + b * a + b * -b = a ^ 2 - b ^ 2
-- rw [add_assoc (a * a)]
--    ⊢ a * a + (-(a * b) + b * a) + b * -b = a ^ 2 - b ^ 2
-- rw [mul_comm b a]
--    ⊢ a * a + (-(a * b) + a * b) + b * -b = a ^ 2 - b ^ 2
-- rw [neg_add_self]
--    ⊢ a * a + 0 + b * -b = a ^ 2 - b ^ 2
-- rw [add_zero]
--    ⊢ a * a + b * -b = a ^ 2 - b ^ 2
-- rw [← pow_two]
--    ⊢ a ^ 2 + b * -b = a ^ 2 - b ^ 2
-- rw [mul_neg_eq_neg_mul_symm]
--    ⊢ a ^ 2 + -(b * b) = a ^ 2 - b ^ 2
-- rw [← pow_two]
--    ⊢ a ^ 2 + -b ^ 2 = a ^ 2 - b ^ 2
-- rw [← sub_eq_add_neg]
--    goals accomplished
</pre>

<b>Comentarios (a partir de los generados por ChatGPT)</b>


<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 8.
