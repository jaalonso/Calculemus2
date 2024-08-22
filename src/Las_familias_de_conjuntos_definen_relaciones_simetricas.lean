-- Las_familias_de_conjuntos_definen_relaciones_simetricas.lean
-- Las familias de conjuntos definen relaciones simétricas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Lean por
--    def relacion (P : set (set X)) (x y : X) :=
--      ∃ A ∈ P, x ∈ A ∧ y ∈ A
--
-- Demostrar que si P es una familia de subconjuntos de X, entonces la
-- relación definida por P es simétrica.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ X tales que x e y están relacionado mediante la relación
-- definida por P. Entonces, existe A tal que
--    A ∈ P ∧ x ∈ A ∧ y ∈ A
-- Por tanto,
--    A ∈ P ∧ y ∈ A ∧ x ∈ A
-- es decir, y y x están relacionado mediante la relación definida por
-- P.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

-- 1ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, h1⟩
  -- A : Set X
  -- h1 : A ∈ P ∧ x ∈ A ∧ y ∈ A
  have h2 : A ∈ P ∧ y ∈ A ∧ x ∈ A := by tauto
  exact ⟨A, h2⟩

-- 2ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  unfold Symmetric
  -- ⊢ ∀ ⦃x y : X⦄, relacion P x y → relacion P y x
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  unfold relacion at *
  -- hxy : ∃ A, A ∈ P ∧ x ∈ A ∧ y ∈ A
  -- ⊢ ∃ A, A ∈ P ∧ y ∈ A ∧ x ∈ A
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  use A

-- 3ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  use A

-- 4ª demostración
-- ===============

example : Symmetric (relacion P) :=
by
  intros x y hxy
  -- x y : X
  -- hxy : relacion P x y
  -- ⊢ relacion P y x
  rcases hxy with ⟨A, hAP, ⟨hxA, hyA⟩⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  -- hyA : y ∈ A
  exact ⟨A, ⟨hAP, hyA, hxA⟩⟩
