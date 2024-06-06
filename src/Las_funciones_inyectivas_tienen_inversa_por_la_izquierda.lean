-- Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.lean
-- Las funciones inyectivas tienen inversa por la izquierda
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-junio-2024
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
-- Demostrar que si f es una función inyectiva con dominio no vacío,
-- entonces f tiene inversa por la izquierda.
-- ---------------------------------------------------------------------

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
  classical
  unfold HasLeftInverse
  let g := fun y ↦ if h : ∃ x, f x = y then some h else choice hα
  use g
  unfold LeftInverse
  intro a
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl
  dsimp at *
  dsimp [g]
  rw [dif_pos] h1
  apply hf
  exact some_spec h1
end

-- 2ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  classical
  let g := λ y, if h : ∃ x, f x = y then some h else choice hα
  use g
  intro a
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl
  dsimp [g]
  rw dif_pos h1
  exact hf (some_spec h1)
end

-- 3ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  unfold HasLeftInverse
  use inv_fun f
  unfold LeftInverse
  intro x
  apply hf
  apply inv_fun_eq
  use x
end

-- 4ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
by
  use inv_fun f
  intro x
  apply hf
  apply inv_fun_eq
  use x
end

-- 5ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
⟨inv_fun f, LeftInverse_inv_fun hf⟩

-- 6ª demostración
-- ===============

example
  [hα : Nonempty α]
  (hf : Injective f)
  : HasLeftInverse f :=
Injective.HasLeftInverse hf
