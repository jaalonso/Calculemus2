-- Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.lean
-- Las clases de equivalencia de elementos relacionados son iguales
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos relacionados
-- son iguales.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ X tales que
--    xRy                                                            (1)
-- Tenemos que demostrar que [x] = [y]; es decir, que
--    [y] ⊆ [x]                                                      (2)
--    [x] ⊆ [y]                                                      (3)
--
-- Para demostrar (2), sea z ∈ [y]. Entonces,
--    yRz
-- entonces, por (1) y por ser R transitiva,
--    xRz
-- Luego, z ∈ [x].
--
-- Para demostrar (2), se observa que por (1) y por ser R simétrica, se
-- tiene que yRx y se puede usar el mismo razonamiento del caso
-- anterior.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- En la demostración se usará el siguiente lema del que se presentan
-- varias demostraciones.

-- 1ª demostración del lema auxiliar
-- =================================

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
by
  intros z hz
  -- z : X
  -- hz : z ∈ clase R y
  -- ⊢ z ∈ clase R x
  have hyz : R y z := hz
  have htrans : Transitive R := Equivalence.transitive h
  have hxz : R x z := htrans hxy hyz
  exact hxz

-- 2ª demostración del lema auxiliar
-- =================================

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
by
  intros z hz
  -- z : X
  -- hz : z ∈ clase R y
  -- ⊢ z ∈ clase R x
  exact (Equivalence.transitive h) hxy hz

-- 3ª demostración del lema auxiliar
-- =================================

lemma aux
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
fun _ hz ↦ (Equivalence.transitive h) hxy hz

-- A continuación se presentan varias demostraciones del ejercicio
-- usando el lema auxiliar

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
by
  apply le_antisymm
  . -- ⊢ clase R x ≤ clase R y
    have hs : Symmetric R := Equivalence.symmetric h
    have hyx : R y x := hs hxy
    exact aux h hyx
  . -- ⊢ clase R y ≤ clase R x
    exact aux h hxy

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
by
  apply le_antisymm
  . -- ⊢ clase R x ≤ clase R y
    exact aux h (Equivalence.symmetric h hxy)
  . -- ⊢ clase R y ≤ clase R x
    exact aux h hxy

-- 3ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : R x y)
  : clase R x = clase R y :=
le_antisymm (aux h (Equivalence.symmetric h hxy)) (aux h hxy)

-- Lemas usados
-- ============

-- variable (x y z : Set X)
-- #check (Equivalence.symmetric : Equivalence R → Symmetric R)
-- #check (Equivalence.transitive : Equivalence R → Transitive R)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
