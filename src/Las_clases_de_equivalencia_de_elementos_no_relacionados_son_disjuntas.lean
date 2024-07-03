-- Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.lean
-- Las clases de equivalencia de elementos no relacionados son disjuntas
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-julio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que las clases de equivalencia de elementos no relacionados
-- son disjuntas.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sean x, y ∈ X tales que no están relacionados mediante la relación
-- R. Tenemos que demostrar que [x] e [y] son disjuntas; es decir,
--    (∀x)[z ∉ [x] ∩ [y]]
-- Para ello, supongamos que un z ∈ [x] ∩ [y]. Luego, z ∈ [x] y z ∈ [y];
-- es decir, se tiene que
--    xRz                                                            (1)
--    yRz                                                            (2)
-- De (2) y la simetría de R, se tiene
--    zRy                                                            (3)
-- De (1), (3) y la transitividad de R, se tiene
--    xRy
-- que es una contradicción,

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X : Type}
variable {x y: X}
variable {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

-- 1ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  have h1 : ∀ z, ¬z ∈ clase R x ∩ clase R y := by
    intro z hz
    -- z : X
    -- hz : z ∈ clase R x ∩ clase R y
    have hxz : R x z := hz.1
    have hyz : R y z := hz.2
    have hzy : R z y := h.2 hyz
    have hxy2 : R x y := h.3 hxz hzy
    exact hxy hxy2
  exact Set.eq_empty_iff_forall_not_mem.mpr h1

-- 2ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  rcases h with ⟨-, hs, ht⟩
  -- hs : ∀ {x y : X}, R x y → R y x
  -- ht : ∀ {x y z : X}, R x y → R y z → R x z
  by_contra h1
  -- h1 : ¬clase R x ∩ clase R y = ∅
  -- ⊢ False
  apply hxy
  -- ⊢ R x y
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y
  . contrapose h1
    -- h1 : ¬∃ z, z ∈ clase R x ∩ clase R y
    -- ⊢ ¬¬clase R x ∩ clase R y = ∅
    push_neg
    push_neg at h1
    -- h1 : ∀ (z : X), ¬z ∈ clase R x ∩ clase R y
    exact Set.eq_empty_iff_forall_not_mem.mpr h1
  rcases h2 with ⟨z, hxz, hyz⟩
  -- z : X
  -- hxz : z ∈ clase R x
  -- hyz : z ∈ clase R y
  replace hxz : R x z := hxz
  replace hyz : R y z := hyz
  have hzy : R z y := hs hyz
  exact ht hxz hzy

-- 3ª demostración
-- ===============

example
  (h : Equivalence R)
  (hxy : ¬ R x y)
  : clase R x ∩ clase R y = ∅ :=
by
  rcases h with ⟨-, hs, ht⟩
  -- hs : ∀ {x y : X}, R x y → R y x
  -- ht : ∀ {x y z : X}, R x y → R y z → R x z
  by_contra h1
  -- h1 : ¬clase R x ∩ clase R y = ∅
  -- ⊢ False
  have h2 : ∃ z, z ∈ clase R x ∩ clase R y
  . aesop (add norm Set.eq_empty_iff_forall_not_mem)
  apply hxy
  -- ⊢ R x y
  rcases h2 with ⟨z, hxz, hyz⟩
  -- z : X
  -- hxz : z ∈ clase R x
  -- hyz : z ∈ clase R y
  exact ht hxz (hs hyz)

-- Lemas usados
-- ============

-- variable (s : Set X)
-- #check (Set.eq_empty_iff_forall_not_mem : s = ∅ ↔ ∀ x, x ∉ s)
