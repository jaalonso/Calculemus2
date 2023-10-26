-- Producto_por_escalar_acotado_superiormente.lean
-- Si c ≥ 0 y f está acotada superiormente, entonces c·f también lo está.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-noviembre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si c ≥ 0 y f está acotada superiormente, entonces c * f
-- también lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema:
--    CotaSuperior_mul : CotaSuperior f a → c ≥ 0 → CotaSuperior (fun x ↦ c * f x) (c * a)
--
-- Puesto que f está acotada superiormente, tiene una cota superior. Sea
-- a una de dichas cotas. Entonces, por el lema CotaSuperior_mul, ca es una cota
-- superior de cf. Por consiguiente, cf está acotada superiormente.

-- Demostraciones con Lean4
-- ========================

import src.Cota_superior_de_producto_por_escalar

variable {f : ℝ → ℝ}
variable {c : ℝ}

-- (acotadaSup f) afirma que f tiene cota superior.
def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

-- 1ª demostración
example
  (hf : acotadaSup f)
  (hc : c ≥ 0)
  : acotadaSup (fun x ↦ c * f x) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : CotaSuperior f a
  have h1 : CotaSuperior (fun x ↦ c * f x) (c * a) :=
    CotaSuperior_mul ha hc
  have h2 : ∃ z, ∀ x, (fun x ↦ c * f x) x ≤ z :=
    Exists.intro (c * a) h1
  show acotadaSup (fun x ↦ c * f x)
  exact h2

-- 2ª demostración
example
  (hf : acotadaSup f)
  (hc : c ≥ 0)
  : acotadaSup (fun x ↦ c * f x) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : CotaSuperior f a
  use c * a
  -- ⊢ CotaSuperior (fun x => c * f x) (c * a)
  apply CotaSuperior_mul ha hc

-- 3ª demostración
example
  (hf : acotadaSup f)
  (hc : c ≥ 0)
  : acotadaSup (fun x ↦ c * f x) :=
by
  rcases hf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : CotaSuperior f a
  exact ⟨c * a, CotaSuperior_mul ha hc⟩

-- 4ª demostración
example
  (hc : c ≥ 0)
  : acotadaSup f → acotadaSup (fun x ↦ c * f x) :=
by
  rintro ⟨a, ha⟩
  -- a : ℝ
  -- ha : CotaSuperior f a
  exact ⟨c * a, CotaSuperior_mul ha hc⟩

-- 5ª demostración
example
  (hc : c ≥ 0)
  : acotadaSup f → acotadaSup (fun x ↦ c * f x) :=
fun ⟨a, ha⟩ ↦ ⟨c * a, CotaSuperior_mul ha hc⟩

-- Lemas usados
-- ============

-- #check (CotaSuperior_mul : CotaSuperior f a → c ≥ 0 → CotaSuperior (fun x ↦ c * f x) (c * a))
