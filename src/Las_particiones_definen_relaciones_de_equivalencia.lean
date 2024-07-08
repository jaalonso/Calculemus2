-- Las_particiones_definen_relaciones_de_equivalencia.lean
-- Las particiones definen relaciones de equivalencia
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-julio-2024
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
-- definida por P es una relación de equivalencia.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea R la relación definida por P. Tenemos que demostrar que R es
-- reflexiva, simétrica y transitiva.
--
-- Para demostrar que R es reflexiva, sea x ∈ X. Puesto que P es una
-- partición de X, existe un A ∈ P tal que x ∈ A. Por tanto, se tiene que
--    (∃ A ∈ P) [x ∈ A ∧ x ∈ A]
-- Luego, xRx.
--
-- Para demostrar que R es simétrica, sean x, y ∈ X tales que xRy.
-- Entonces, existe A tal que
--    A ∈ P ∧ x ∈ A ∧ y ∈ A
-- Por tanto,
--    A ∈ P ∧ y ∈ A ∧ x ∈ A
-- es decir, yRx.
--
-- Para demostrar que R es transitiva, sean x, y, z ∈ X tales que xRy e
-- yRz. Entonces, existen B₁ y B₂ tales que
--    B₁ ∈ P ∧ x ∈ B₁ ∧ y ∈ B₁                                       (1)
--    B₂ ∈ P ∧ y ∈ B₂ ∧ z ∈ B₂                                       (2)
-- Si demostramos que B₁ = B₂, se tiene que
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

example
  (h : particion P)
  : Equivalence (relacion P) :=
by
  set R := relacion P
  repeat' constructor
  . -- ⊢ ∀ (x : X), R x x
    intro x
    -- x : X
    -- ⊢ R x x
    rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
    -- A : Set X
    -- hAP : A ∈ P
    -- hxA : x ∈ A
    -- ⊢ R x x
    exact ⟨A, ⟨hAP, hxA, hxA⟩⟩
  . -- ⊢ ∀ {x y : X}, R x y → R y x
    intros x y hxy
    -- x y : X
    -- hxy : R x y
    -- ⊢ R y x
    rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩
    -- B : Set X
    -- hBP : B ∈ P
    -- hxB : x ∈ B
    -- hyB : y ∈ B
    exact ⟨B, ⟨hBP, hyB, hxB⟩⟩
  . -- ⊢ ∀ {x y z : X}, R x y → R y z → R x z
    rintro x y z ⟨B1, hB1P, hxB1, hyB1⟩ ⟨B2, hB2P, hyB2, hzB2⟩
    -- x y z : X
    -- B1 : Set X
    -- hB1P : B1 ∈ P
    -- hxB1 : x ∈ B1
    -- hyB1 : y ∈ B1
    -- B2 : Set X
    -- hB2P : B2 ∈ P
    -- hyB2 : y ∈ B2
    -- hzB2 : z ∈ B2
    -- ⊢ R x z
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

-- 2ª demostración
-- ===============

example
  (h : particion P)
  : Equivalence (relacion P) :=
by
  set R := relacion P
  repeat' constructor
  . -- ⊢ ∀ (x : X), R x x
    intro x
    -- x : X
    -- ⊢ R x x
    rcases (h.1 x) with ⟨A, hAP, hxA, -⟩
    -- A : Set X
    -- hAP : A ∈ P
    -- hxA : x ∈ A
    -- ⊢ R x x
    exact ⟨A, ⟨hAP, hxA, hxA⟩⟩
  . -- ⊢ ∀ {x y : X}, R x y → R y x
    intros x y hxy
    -- x y : X
    -- hxy : R x y
    -- ⊢ R y x
    rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩
    -- B : Set X
    -- hBP : B ∈ P
    -- hxB : x ∈ B
    -- hyB : y ∈ B
    exact ⟨B, ⟨hBP, hyB, hxB⟩⟩
  . -- ⊢ ∀ {x y z : X}, R x y → R y z → R x z
    rintro x y z ⟨B1, hB1P, hxB1, hyB1⟩ ⟨B2, hB2P, hyB2, hzB2⟩
    -- x y z : X
    -- B1 : Set X
    -- hB1P : B1 ∈ P
    -- hxB1 : x ∈ B1
    -- hyB1 : y ∈ B1
    -- B2 : Set X
    -- hB2P : B2 ∈ P
    -- hyB2 : y ∈ B2
    -- hzB2 : z ∈ B2
    -- ⊢ R x z
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

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.trans : x = y → y = z → x = z)
