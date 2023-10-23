-- Suma_de_funciones_acotadas_inferiormente.lean
-- La suma de dos funciones acotadas inferiormente también lo está.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 31-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de dos funciones acotadas inferiormente también
-- lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Del ejercicio "La suma de una cota inferior de f y una cota inferior
-- de g es una cota inferior de f+g" usaremos la definición de cota
-- inferior (CotaInferior) y el lema sumaCotaInf.
--
-- Puesto que f está acotada inferiormente, tiene una cota inferior. Sea
-- a una de dichas cotas. Análogamentte, puesto que g está acotada
-- inferiormente, tiene una cota inferior. Sea b una de dichas
-- cotas. Por el lema FnLb_add, a+b es una cota inferior de f+g. Por
-- consiguiente, f+g está acotada inferiormente.

-- Demostraciones con Lean4
-- ========================

import src.Suma_de_cotas_inferiores
variable {f g : ℝ → ℝ}

-- (acotadaInf f) afirma que f tiene cota inferior.
def acotadaInf (f : ℝ → ℝ) :=
  ∃ a, CotaInferior f a

-- 1ª demostración
example
  (hf : acotadaInf f)
  (hg : acotadaInf g)
  : acotadaInf (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : CotaInferior f a
  cases' hg with b hb
  -- b : ℝ
  -- hb : CotaInferior g b
  have h1 : CotaInferior (f + g) (a + b) := sumaCotaInf ha hb
  have h2 : ∃ z, CotaInferior (f + g) z :=
    Exists.intro (a + b) h1
  show acotadaInf (f + g)
  exact h2

-- 2ª demostración
example
  (hf : acotadaInf f)
  (hg : acotadaInf g)
  : acotadaInf (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : FnLb f a
  cases' hg with b hgb
  -- b : ℝ
  -- hgb : FnLb g b
  use a + b
  -- ⊢ FnLb (f + g) (a + b)
  apply sumaCotaInf ha hgb

-- 3ª demostración
example
  (hf : acotadaInf f)
  (hg : acotadaInf g)
  : acotadaInf (f + g) :=
by
  rcases hf with ⟨a, ha⟩
  -- a : ℝ
  -- ha : FnLb f a
  rcases hg with ⟨b, hb⟩
  -- b : ℝ
  -- hb : FnLb g b
  exact ⟨a + b, sumaCotaInf ha hb⟩

-- 4ª demostración
example :
  acotadaInf f → acotadaInf g → acotadaInf (f + g) :=
by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  -- a : ℝ
  -- ha : FnLb f a
  -- b : ℝ
  -- hb : FnLb g b
  exact ⟨a + b, sumaCotaInf ha hb⟩

-- 5ª demostración
example :
  acotadaInf f → acotadaInf g → acotadaInf (f + g) :=
fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, sumaCotaInf ha hb⟩

-- Lemas usados
-- ============

-- #check (sumaCotaInf : FnLb f a → FnLb g b → FnLb (f + g) (a + b))
