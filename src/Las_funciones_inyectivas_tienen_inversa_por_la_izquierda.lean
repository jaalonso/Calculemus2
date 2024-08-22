-- Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.lean
-- Las funciones inyectivas tienen inversa por la izquierda.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, que g es una inversa por la izquierda de f está definido por
--    LeftInverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- y que f tenga inversa por la izquierda está definido por
--    HasLeftInverse (f : α → β) : Prop :=
--       ∃ finv : β → α, LeftInverse finv f
-- Finalmente, que f es inyectiva está definido por
--    Injective (f : α → β) : Prop :=
--       ∀ ⦃x y⦄, f x = f y → x = y
--
-- Demostrar que si f es una función inyectiva con dominio no vacío,
-- entonces f tiene inversa por la izquierda.
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

import Mathlib.Tactic

open Function Classical

variable {α β: Type _}
variable {f : α → β}

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
