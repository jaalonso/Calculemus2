-- Cota_superior_de_producto_por_escalar.lean
-- Si a es una cota superior de f y c ≥ 0, entonces ca es una cota superior de cf.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una cota superior de f y c ≥ 0,
-- entonces c * a es una cota superior de c * f.
-- ----------------------------------------------------------------------

-- Demostración en lenguaj natural
-- ===============================

-- Se usará el lema
--    {b ≤ c, 0 ≤ a} ⊢ ab ≤ ac                                      (L1)
--
-- Tenemos que demostrar que
--    (∀ y ∈ ℝ) cf(y) ≤ ca.
-- Sea y ∈ R. Puesto que a es una cota de f, se tiene que
--    f(y) ≤ a
-- que, junto con c ≥ 0, por el lema L1 nos da
--    cf(y) ≤ ca

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

variable {f : ℝ → ℝ}
variable {c : ℝ}

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
example
  (hfa : CotaSuperior f a)
  (h : c ≥ 0)
  : CotaSuperior (fun x ↦ c * f x) (c * a) :=
by
  intro y
  -- y : ℝ
  -- ⊢ (fun x => c * f x) y ≤ c * a
  have ha : f y ≤ a := hfa y
  calc (fun x => c * f x) y
       = c * f y := by rfl
     _ ≤ c * a   := mul_le_mul_of_nonneg_left ha h

-- 2ª demostración
example
  (hfa : CotaSuperior f a)
  (h : c ≥ 0)
  : CotaSuperior (fun x ↦ c * f x) (c * a) :=
by
  intro y
  calc (fun x => c * f x) y
       = c * f y := by rfl
     _ ≤ c * a   := mul_le_mul_of_nonneg_left (hfa y) h

-- 3ª demostración
example
  (hfa : CotaSuperior f a)
  (h : c ≥ 0)
  : CotaSuperior (fun x ↦ c * f x) (c * a) :=
by
  intro y
  show (fun x => c * f x) y ≤ c * a
  exact mul_le_mul_of_nonneg_left (hfa y) h

-- 4ª demostración
lemma CotaSuperior_mul
  (hfa : CotaSuperior f a)
  (h : c ≥ 0)
  : CotaSuperior (fun x ↦ c * f x) (c * a) :=
fun y ↦ mul_le_mul_of_nonneg_left (hfa y) h

-- Lemas usados
-- ============

-- variable (c : ℝ)
-- #check (mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c)
