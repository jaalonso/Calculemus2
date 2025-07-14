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
open Function Classical

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

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función inyectiva con dominio no
-- vacío, entonces f tiene inversa por la izquierda.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f: A → B inyectiva con A ≠ ∅. Entonces, existe un a ∈ A. Sea
-- g: B → A definida por
--    g(y) = + un x tal que f(x) = y, si (∃x)[f(x) = y]
--           + a, en caso contrario.
-- Vamos a demostrar que g es una inversa por la izquierda de f; es
-- decir,
--    (∀x)[g(f(x)) = x]
-- Para ello, sea x ∈ A. Entonces,
--    (∃x)[f(x) = f(x)]
-- Por la definición de g,
--    g(f(x)) = z                                                    (1)
-- donde
--    f(z) = f(x).
-- Como f es inyectiva,
--    z = x
-- Y, por (1),
--    g(f(x)) = x

-- Demostraciones con Lean4
-- ========================

-- 1ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  unfold HasLeftInverse
  -- ⊢ ∃ finv, LeftInverse finv f
  set g := fun y ↦ if h : ∃ x, f x = y then h.choose else Classical.arbitrary α
  use g
  unfold LeftInverse
  -- ⊢ ∀ (x : α), g (f x) = x
  intro a
  -- ⊢ g (f a) = a
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl
  simp only [g] at *
  -- ⊢ (if h : ∃ x, f x = f a then Exists.choose h else Classical.arbitrary α) = a
  simp [h1]
  -- ⊢ Exists.choose (_ : ∃ x, f x = f a) = a
  apply hf
  -- ⊢ f (Exists.choose (_ : ∃ x, f x = f a)) = f a
  exact Classical.choose_spec h1

-- 2ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  set g := fun y ↦ if h : ∃ x, f x = y then h.choose else Classical.arbitrary α
  use g
  -- ⊢ LeftInverse g f
  intro a
  -- a : α
  -- ⊢ g (f a) = a
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl
  simp only [g] at *
  -- ⊢ (if h : ∃ x, f x = f a then Exists.choose h else Classical.arbitrary α) = a
  simp [h1]
  -- ⊢ Exists.choose (_ : ∃ x, f x = f a) = a
  exact hf (Classical.choose_spec h1)

-- 3ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  unfold HasLeftInverse
  -- ⊢ ∃ finv, LeftInverse finv f
  use invFun f
  -- ⊢ LeftInverse (invFun f) f
  unfold LeftInverse
  -- ⊢ ∀ (x : α), invFun f (f x) = x
  intro x
  -- x : α
  -- ⊢ invFun f (f x) = x
  apply hf
  -- ⊢ f (invFun f (f x)) = f x
  apply invFun_eq
  -- ⊢ ∃ a, f a = f x
  use x

-- 4ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  use invFun f
  -- ⊢ LeftInverse (invFun f) f
  intro x
  -- x : α
  -- ⊢ invFun f (f x) = x
  apply hf
  -- ⊢ f (invFun f (f x)) = f x
  apply invFun_eq
  -- ⊢ ∃ a, f a = f x
  use x

-- 5ª demostración
-- ===============

example
  [_hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
⟨invFun f, leftInverse_invFun hf⟩

-- 6ª demostración
-- ===============

example
  [_hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
Injective.hasLeftInverse hf

-- Lemas usados
-- ============

-- variable (p : α → Prop)
-- variable (x : α)
-- variable (b : β)
-- variable (γ : Type _) [Nonempty γ]
-- variable (f1 : γ → β)
-- #check (Classical.choose_spec : (h : ∃ x, p x) → p (Classical.choose h))
-- #check (Exists.intro x: p x → ∃ y, p y)
-- #check (Injective.hasLeftInverse : Injective f1 → HasLeftInverse f1)
-- #check (invFun_eq : (∃ a, f1 a = b) → f1 (invFun f1 b) = b)
-- #check (leftInverse_invFun : Function.Injective f1 → LeftInverse (Function.invFun f1) f1)
