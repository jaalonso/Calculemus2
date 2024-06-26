-- La_igualdad_de_valores_es_una_relacion_de_equivalencia.lean
-- La igualdad de valores es una relación de equivalencia.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean X e Y dos conjuntos y f una función de X en Y. Se define la
-- relación R en X de forma que x está relacionado con y si f(x) = f(y).
--
-- Demostrar que R es una relación de equivalencia.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que R es reflexiva, simétrica y transitiva,
--
-- Para demostrar que R es reflexiva, sea x ∈ X. Entonces, f(x) = f(x)
-- y, por tanto xRx.
--
-- Para demostrar que R es simétrica, sean x, y ∈ X tales que xRy.
-- Entonces, f(x) = f(y). Luego, f(y) = f(x) y, por tanto, yRx.
--
-- Para demostrar que R es transitiva, sean x, y, z ∈ X tales que xRy y
-- yRz. Entonces, f(x) = f(y) y f(y) = f(z). Luego, f(x) = f(z) y, por
-- tanto, zRz.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic

variable {X Y : Type _}
variable (f : X → Y)

def R (x y : X) :=
  f x = f y

-- 1ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    intro x
    -- x : X
    -- ⊢ R f x x
    unfold R
    -- ⊢ f x = f x
    exact Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    intros x y hxy
    -- x y : X
    -- hxy : R f x y
    -- ⊢ R f y x
    unfold R at *
    -- hxy : f x = f y
    -- ⊢ f y = f x
    exact Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    intros x y z hxy hyz
    -- x y z : X
    -- hxy : R f x y
    -- hyz : R f y z
    -- ⊢ R f x z
    unfold R at *
    -- hxy : f x = f y
    -- hyz : f y = f z
    -- ⊢ f x = f z
    exact Eq.trans hxy hyz

-- 2ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    intro x
    -- x : X
    -- ⊢ R f x x
    exact Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    intros x y hxy
    -- x y : X
    -- hxy : R f x y
    -- ⊢ R f y x
    exact Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    intros x y z hxy hyz
    -- x y z : X
    -- hxy : R f x y
    -- hyz : R f y z
    -- ⊢ R f x z
    exact Eq.trans hxy hyz

-- 3ª demostración
-- ===============

example : Equivalence (R f) :=
by
  repeat' constructor
  . -- ⊢ ∀ (x : X), R f x x
    exact fun x ↦ Eq.refl (f x)
  . -- ⊢ ∀ {x y : X}, R f x y → R f y x
    exact fun hxy ↦ Eq.symm hxy
  . -- ⊢ ∀ {x y z : X}, R f x y → R f y z → R f x z
    exact fun hxy hyz ↦ by exact  Eq.trans hxy hyz

-- 4ª demostración
-- ===============

example : Equivalence (R f) :=
⟨fun x ↦ Eq.refl (f x),
 fun hxy ↦ Eq.symm hxy,
 fun hxy hyz ↦ Eq.trans hxy hyz⟩

-- Lemas usados
-- ============

-- variable (x y z : X)
-- #check (Eq.refl x : x = x)
-- #check (Eq.symm : x = y → y = x)
-- #check (Eq.trans : x = y → y = z → x = z)
