-- Las_particiones_definen_relaciones_transitivas.lean
-- Las particiones definen relaciones transitivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 8-julio-2024
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
-- definida por P es transitiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea R la relación definida por P y x, y, z ∈ X tales que xRy e yRz.
-- Entonces, existen B₁ y B₂ tales que
--    B₁ ∈ P ∧ x ∈ B₁ ∧ y ∈ B₁                                       (1)
--    B₂ ∈ P ∧ y ∈ B₂ ∧ z ∈ B₂                                       (2)
-- Si demostamos que B₁ = B₂, se tiene que
--    B₁ ∈ P ∧ x ∈ B₁ ∧ z ∈ B₁
-- y, por tanto, xRz.
--
-- Para demostrar que B₁ = B₂, se observa que, por ser P una partición
-- de X, se tiene
--    (∀ x ∈ X)(∃ B ∈ P)(∀ C ∈ P)[x ∈ C → B = C]
-- por tanto, para y, existe un B ∈ P tal que
--    (∀ C ∈ P)[y ∈ C → B = C]                                       (3)
-- Entonces, de (3) y (1), se tiene
--    B₁ = B     [de (3) y (1)]
--       = B₂    [de (3) y (2)]

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
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  have h1 : B1 = B2 := by
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    calc B1 = B  := by exact (hB B1 hB1P hyB1).symm
          _ = B2 := hB B2 hB2P hyB2
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    rw [h1]
    -- ⊢ z ∈ B2
    exact hzB2

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  unfold Transitive
  -- ⊢ ∀ ⦃x y z : X⦄, relacion P x y → relacion P y z → relacion P x z
  intros x y z h1 h2
  -- x y z : X
  -- h1 : relacion P x y
  -- h2 : relacion P y z
  -- ⊢ relacion P x z
  unfold relacion at *
  -- h1 : ∃ A, A ∈ P ∧ x ∈ A ∧ y ∈ A
  -- h2 : ∃ A, A ∈ P ∧ y ∈ A ∧ z ∈ A
  -- ⊢ ∃ A, A ∈ P ∧ x ∈ A ∧ z ∈ A
  rcases h1 with ⟨B1, hB1P, hxB1, hyB1⟩
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  rcases h2 with ⟨B2, hB2P, hyB2, hzB2⟩
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  use B1
  -- ⊢ B1 ∈ P ∧ x ∈ B1 ∧ z ∈ B1
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    convert hzB2
    -- ⊢ B1 = B2
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    have hBB1 : B = B1 := hB B1 hB1P hyB1
    have hBB2 : B = B2 := hB B2 hB2P hyB2
    exact Eq.trans hBB1.symm hBB2

-- 3ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  use B1
  -- ⊢ B1 ∈ P ∧ x ∈ B1 ∧ z ∈ B1
  repeat' constructor
  . -- ⊢ B1 ∈ P
    exact hB1P
  . -- ⊢ x ∈ B1
    exact hxB1
  . -- ⊢ z ∈ B1
    convert hzB2
    -- ⊢ B1 = B2
    rcases (h.1 y) with ⟨B, -, -, hB⟩
    -- B : Set X
    -- hB : ∀ (C : Set X), C ∈ P → y ∈ C → B = C
    exact Eq.trans (hB B1 hB1P hyB1).symm (hB B2 hB2P hyB2)

-- 4ª demostración
-- ===============

example
  (h : particion P)
  : Transitive (relacion P) :=
by
  rintro x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩
  -- x y z : X
  -- B1 : Set X
  -- hB1P : B1 ∈ P
  -- hxB1 : x ∈ B1
  -- hyB1 : y ∈ B1
  -- B2 : Set X
  -- hB2P : B2 ∈ P
  -- hyB2 : y ∈ B2
  -- hzB2 : z ∈ B2
  -- ⊢ relacion P x z
  exact ⟨B1, ⟨hB1P,
              hxB1,
              by { convert hzB2
                   rcases (h.1 y) with ⟨B, -, -, hB⟩
                   exact Eq.trans (hB B1 hB1P hyB1).symm
                                  (hB B2 hB2P hyB2) }⟩⟩

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.trans : x = y → y = z → x = z)
