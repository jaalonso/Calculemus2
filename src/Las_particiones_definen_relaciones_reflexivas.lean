-- Las_particiones_definen_relaciones_reflexivas.lean
-- Las particiones definen relaciones reflexivas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Cada familia de conjuntos P define una relación de forma que dos
-- elementos están relacionados si algún conjunto de P contiene a ambos
-- elementos. Se puede definir en Lean por
--    def relacion (P : set (set X)) (x y : X) :=
--      ∃ A ∈ P, x ∈ A ∧ y ∈ A
--
-- Una familia de subconjuntos de X es una partición de X si cada elemento
-- de X pertenece a un único conjunto de P y todos los elementos de P
-- son no vacíos. Se puede definir en Lean por
--    def particion (P : set (set X)) : Prop :=
--      (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
--
-- Demostrar que si P es una partición de X, entonces la relación
-- definida por P es reflexiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ X. Puesto que P es una partición de X, existe un A ∈ P tal
-- que x ∈ A. Por tanto, se tiene que
--    (∃ A ∈ P) [x ∈ A ∧ x ∈ A]
-- Luego, x está relacionado con x mediante la relación definia por P.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X : Type}
variable (P : Set (Set X))

def relacion (P : Set (Set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

-- 1ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- x : X
  -- ⊢ relacion P x x
  rcases h.1 x with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  exact ⟨A, hAP, hxA, hxA⟩

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  unfold Reflexive
  -- ⊢ ∀ (x : X), relacion P x x
  intro x
  -- x : X
  -- ⊢ relacion P x x
  unfold relacion
  -- ⊢ ∃ A, A ∈ P ∧ x ∈ A ∧ x ∈ A
  unfold particion at h
  -- h : (∀ x, ∃ B, B ∈ P ∧ x ∈ B ∧ ∀ C, C ∈ P → x ∈ C → B = C) ∧ ¬∅ ∈ P
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x
  rcases h with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A

-- 3ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- ⊢ relacion P x x
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x
  rcases h with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A

-- 4ª demostración
-- ===============

example
  (h : particion P)
  : Reflexive (relacion P) :=
by
  intro x
  -- x : X
  -- ⊢ relacion P x x
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
  -- A : Set X
  -- hAP : A ∈ P
  -- hxA : x ∈ A
  use A
