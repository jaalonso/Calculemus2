-- Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.lean
-- Las funciones con inversa por la izquierda son inyectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, que g es una inversa por la izquierda de f está definido por
--    LeftInverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- y que f tenga inversa por la izquierda está definido por
--    HasLeftInverse (f : α → β) : Prop :=
--       ∃ finv : β → α, LeftInverse finv f
-- Finalmente, que f es inyectiva está definido por
--    Injective (f : α → β) : Prop :=
--       ∀ ⦃x y⦄, f x = f y → x = y
--
-- Demostrar que si f tiene inversa por la izquierda, entonces f es
-- inyectiva.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f: A → B que tiene inversa por la izquierda. Entonces, existe
-- una g: B → A tal que
--    (∀ x ∈ A)[g(f(x)) = x]                                         (1)
-- Para demostrar que f es inyectiva, sean x, y ∈ A tales que
--    f(x) = f(y)
-- Entonces,
--    g(f(x)) = g(f(y))
-- y, por (1),
--    x = y

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

universe u v
variable {α : Type u}
variable {β : Type v}
variable {f : α → β}

-- 1ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  intros x y hxy
  -- x y : α
  -- hxy : f x = f y
  -- ⊢ x = y
  unfold HasLeftInverse at hf
  -- hf : ∃ finv, LeftInverse finv f
  unfold LeftInverse at hf
  -- hf : ∃ finv, ∀ (x : α), finv (f x) = x
  cases' hf with g hg
  -- g : β → α
  -- hg :
  calc x = g (f x) := (hg x).symm
       _ = g (f y) := congr_arg g hxy
       _ = y       := hg y

-- 2ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  intros x y hxy
  -- x y : α
  -- hxy : f x = f y
  -- ⊢ x = y
  cases' hf with g hg
  -- g : β → α
  -- hg : LeftInverse g f
  calc x = g (f x) := (hg x).symm
       _ = g (f y) := congr_arg g hxy
       _ = y       := hg y

-- 3ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
by
  apply Exists.elim hf
  -- ⊢ ∀ (a : β → α), LeftInverse a f → Injective f
  intro g hg
  -- g : β → α
  -- hg : LeftInverse g f
  -- ⊢ Injective f
  exact LeftInverse.injective hg

-- 4ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
Exists.elim hf (fun _g hg ↦ LeftInverse.injective hg)

-- 5ª demostración
-- ===============

example
  (hf : HasLeftInverse f)
  : Injective f :=
HasLeftInverse.injective hf

-- Lemas usados
-- ============

-- variable (x y : α)
-- variable (p : α → Prop)
-- variable (b : Prop)
-- variable (g : β → α)
-- #check (Exists.elim : (∃ x, p x) → (∀ x, p x → b) → b)
-- #check (HasLeftInverse.injective : HasLeftInverse f → Injective f)
-- #check (LeftInverse.injective : LeftInverse g f → Injective f)
-- #check (congr_arg f : x = y → f x = f y)
