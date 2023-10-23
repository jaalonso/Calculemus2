-- Suma_de_funciones_acotadas_superiormente.lean
-- La suma de dos funciones acotadas superiormente también lo está.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-octubre-2023
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de dos funciones acotadas superiormente también
-- lo está.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Del ejercicio "La suma de una cota superior de f y una cota superior
-- de g es una cota superior de f+g" (que se encuentra en
-- https://bit.ly/3QauluK ) usaremos la definición de cota superior
-- (CotaSuperior) y el lema sumaCotaSup.
--
-- Puesto que f está acotada superiormente, tiene una cota superior. Sea
-- a una de dichas cotas. Análogamentte, puesto que g está acotada
-- superiormente, tiene una cota superior. Sea b una de dichas
-- cotas. Por el lema sumaCotaSup, a+b es una cota superior de f+g. or
-- consiguiente, f+g está acotada superiormente.

-- Demostraciones con Lean4
-- ========================

-- Nota: Se puede descomentar la siguiente importación y comentar las
-- expresiones que se han anotado como no necesarias si se importa.

-- import src.Suma_de_cotas_superiores

-- Nota: No se necesita si se importa src.Suma_de_cotas_superiores
import Mathlib.Data.Real.Basic

variable {f g : ℝ → ℝ}

-- Nota: No se necesita si se importa src.Suma_de_cotas_superiores
variable {a b : ℝ}

-- Nota: No se necesita si se importa src.Suma_de_cotas_superiores
-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- Nota: No se necesita si se importa src.Suma_de_cotas_superiores
theorem sumaCotaSup
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  : CotaSuperior (f + g) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

-- (acotadaSup f) afirma que f tiene cota superior.
def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

-- 1ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : CotaSuperior f a
  cases' hg with b hb
  -- b : ℝ
  -- hb : CotaSuperior g b
  have h1 : CotaSuperior (f + g) (a + b) :=
    sumaCotaSup ha hb
  have h2 : ∃ z, CotaSuperior (f+g) z :=
    Exists.intro (a + b) h1
  show acotadaSup (f + g)
  exact h2

-- 2ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : FnUb f a
  cases' hg with b hb
  -- b : ℝ
  -- hb : FnUb g b
  use a + b
  apply sumaCotaSup ha hb

-- 4ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨a + b, sumaCotaSup ha hb⟩

-- 5ª demostración
example :
  acotadaSup f → acotadaSup g → acotadaSup (f + g) :=
by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨a + b, sumaCotaSup ha hb⟩

-- 6ª demostración
example :
  acotadaSup f → acotadaSup g → acotadaSup (f + g) :=
fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, sumaCotaSup ha hb⟩

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (sumaCotaSup : CotaSuperior f a → CotaSuperior g b → CotaSuperior (f + g) (a + b))
