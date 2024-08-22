-- El_conjunto_de_las_clases_de_equivalencia_es_una_particion.lean
-- El conjunto de las clases de equivalencia es una partición.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es una relación de equivalencia en X, entonces las
-- clases de equivalencia de R es una partición de X.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea P = {[x] : x ∈ X}. Tenemos que demostrar que P es una partición
-- de X; es decir, que
--    (∀x ∈ X)(∃B ∈ P)[x ∈ B ∧ (∀C ∈ P)[x ∈ C → B = C]                  (1)
--    ∅ ∉ P                                                             (2)
--
-- Para demostrar (1) basta probar que
--    (∀x ∈ X)(∃y ∈ X)[x ∈ [y] ∧ (∀a ∈ X)[x ∈ [a] → [y] = [a]]          (3)
-- Para ello sea x ∈ X. Veamos que [x] cumple las condiciones de (3); es
-- decir,
--    x ∈ [x] ∧ (∀a ∈ X)[x ∈ [a] → [x] = [a]]                           (4)
--
-- La primera condición de (4) se verifica puesto que R es reflexiva.
--
-- Para probar la segunda parte de (4), sea a ∈ X tal que x ∈ [a]; es
-- decir,
--    aRx                                                               (5)
-- y, puesto que R es simétrica,
--    xRa                                                               (6)
-- Entonces,
--    z ∈ [x] ⟹ xRz
--            ⟹ aRz        [por (5) y la transitividad de R]
--            ⟹ z ∈ [a]
--    z ∈ [a] ⟹ aRz
--            ⟹ xRz        [por (6) y la transitividad de R]
--            ⟹ z ∈ [x]
-- Por tanto, [x] = [a].
--
-- Para demostrar (2), supongamos que ∅ ∈ P. Entonces, existe un x ∈ X tal
-- que [x] = ∅ lo cual es imposible porque x ∈ [x].

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (P : Set (Set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

lemma aux
  (h : Equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
fun _ hz ↦ h.3 hxy hz

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  : particion {a : Set X | ∃ s : X, a = clase R s} :=
by
  set P := {a : Set X | ∃ s : X, a = clase R s}
  constructor
  . -- ⊢ (∀ x, ∃ B, B ∈ P) ∧ x ∈ B ∧ (∀ C, C ∈ P → x ∈ C → B = C)
    simp [P]
    -- ⊢ (∀ x, ∃ B, (∃ s, B = clase R s)) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    intro x
    -- x : X
    -- ⊢ ∃ B, (∃ s, B = clase R s) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    use (clase R x)
    -- ⊢ (∃ s, clase R x = clase R s) ∧ x ∈ clase R x ∧ (∀ a, y ∈ clase R a → clase R x = clase R a)
    constructor
    . -- ⊢ ∃ s, clase R x = clase R s
      use x
    . --   x ∈ clase R x ∧
      --   ∀ a, x ∈ clase R a → clase R x = clase R a
      constructor
      . -- ⊢ x ∈ clase R x
        exact h.1 x
      . -- ∀ a, x ∈ clase R a → clase R x = clase R a
        intros a ha
        -- a : X
        -- ha : x ∈ clase R a
        -- ⊢ clase R x = clase R a
        apply le_antisymm
        . -- ⊢ clase R x ≤ clase R a
          exact aux h ha
        . -- ⊢ clase R a ≤ clase R x
          exact aux h (h.2 ha)
  . -- ⊢ ¬∅ ∈ P
    simp [P]
    -- ⊢ ∀ (x : X), ¬∅ = clase R x
    intros x hx
    -- x : X
    -- hx : ∅ = clase R x
    -- ⊢ False
    have h1 : x ∈ clase R x := h.1 x
    rw [←hx] at h1
    -- h1 : x ∈ ∅
    exact Set.not_mem_empty x h1

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  : particion {a : Set X | ∃ s : X, a = clase R s} :=
by
  set P := {a : Set X | ∃ s : X, a = clase R s}
  constructor
  . -- ⊢ (∀ x, ∃ B, B ∈ P) ∧ x ∈ B ∧ (∀ C, C ∈ P → x ∈ C → B = C)
    simp [P]
    -- ⊢ (∀ x, ∃ B, (∃ s, B = clase R s)) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    intro x
    -- x : X
    -- ⊢ ∃ B, (∃ s, B = clase R s) ∧ x ∈ B ∧ (∀ a, x ∈ clase R a → B = clase R a)
    use (clase R x)
    -- ⊢ (∃ s, clase R x = clase R s) ∧ x ∈ clase R y ∧ (∀ a, x ∈ clase R a → clase R x = clase R a)
    repeat' constructor
    . -- ⊢ x ∈ clase R x
      exact h.1 x
    . -- ⊢ ∀ a, x ∈ clase R a → clase R x = clase R a
      intros a ha
      -- a : X
      -- ha : y ∈ clase R a
      -- ⊢ clase R a = clase R a
      exact le_antisymm (aux h ha) (aux h (h.2 ha))
  . -- ⊢ ¬∅ ∈ P
    simp [P]
    -- ⊢ ∀ (x : X), ¬∅ = clase R x
    intros x hx
    -- x : X
    -- hx : ∅ = clase R x
    -- ⊢ False
    have h1 : x ∈ clase R x := h.1 x
    rw [←hx] at h1
    -- h1 : x ∈ ∅
    exact Set.not_mem_empty x h1

-- Lemas usados
-- ============

-- variable (A B : Set X)
-- #check (Set.not_mem_empty x : x ∉ ∅)
-- #check (le_antisymm : A ≤ B → B ≤ A → A = B)
