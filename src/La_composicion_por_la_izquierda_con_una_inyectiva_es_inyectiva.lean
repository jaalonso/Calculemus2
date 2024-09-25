-- La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean
-- La composición por la izquierda con una inyectiva es una operación inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean f₁ y f₂ funciones de X en Y y g una función de Y en Z. Demostrar
-- que si g es inyectiva y g ∘ f₁ = g ∘ f₂, entonces f₁ = f₂.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea x ∈ X. Tenemos que demostrar que
--    f₁(x) = f₂(x)
-- Puesto que g es inyectiva, basta demostrar que
--    g(f₁(x)) = g(f₂(x))
-- que se demuestra mediante la siguiente cadena de igualdades
--    g(f₁(x)) = (g ∘ f₁)(x)
--             = (g ∘ f₂)(x)    [porque g ∘ f₁ = g ∘ f₂]
--             = g(f₂(x))

-- Demostraciones con Lean4
-- ========================

import Mathlib.Tactic
open Function

variable {X Y Z : Type _}
variable {f₁ f₂ : X → Y}
variable {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
by
  funext x
  -- x : X
  -- ⊢ f₁ x = f₂ x
  apply hg
  -- ⊢ g (f₁ x) = g (f₂ x)
  calc g (f₁ x) = (g ∘ f₁) x := by rw [comp_apply]
              _ = (g ∘ f₂) x := congr_fun hgf x
              _ = g (f₂ x)   := by rw [comp_apply]

-- 2ª demostración
-- ===============

example
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
by
  funext x
  -- x : X
  -- ⊢ f₁ x = f₂ x
  apply hg
  -- ⊢ g (f₁ x) = g (f₂ x)
  exact congr_fun hgf x

-- 3ª demostración
-- ===============

example
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
by
  refine' funext (fun x ↦ hg _)
  -- x : X
  -- ⊢ g (f₁ x) = g (f₂ x)
  exact congr_fun hgf x

-- 4ª demostración
-- ===============

example
  (hg : Injective g)
  : Injective (fun f ↦ g ∘ f : (X → Y) → (X → Z)) :=
fun _ _ hgf ↦ funext (fun i ↦ hg (congr_fun hgf i : _))

-- 5ª demostración
-- ===============

example
  [Nonempty Y]
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
calc f₁ = id ∘ f₁         := (id_comp f₁).symm
 _ = (invFun g ∘ g) ∘ f₁  := congrArg (. ∘ f₁) (invFun_comp hg).symm
 _ = invFun g ∘ (g ∘ f₁)  := comp_assoc (invFun g) g f₁
 _ = invFun g ∘ (g ∘ f₂)  := congrArg (invFun g ∘ .) hgf
 _ = (invFun g ∘ g) ∘ f₂  := comp_assoc (invFun g) g f₂
 _ = id ∘ f₂              := congrArg (. ∘ f₂) (invFun_comp hg)
 _ = f₂                   := id_comp f₂

-- 6ª demostración
-- ===============

example
  [Nonempty Y]
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
calc f₁ = id ∘ f₁        := by aesop
 _ = (invFun g ∘ g) ∘ f₁ := by aesop (add norm invFun_comp)
 _ = invFun g ∘ (g ∘ f₁) := by rfl
 _ = invFun g ∘ (g ∘ f₂) := by aesop (add norm hgf)
 _ = (invFun g ∘ g) ∘ f₂ := by rfl
 _ = id ∘ f₂             := by aesop (add norm invFun_comp)
 _ = f₂                  := by aesop

-- Lemas usados
-- ============

-- variable (f : X → Y)
-- variable (x y : X)
-- variable (A B C D : Type _)
-- variable (X' : Type)[Nonempty X']
-- variable (f' : X' → Y)
-- #check (comp_assoc : ∀ (f : C → D) (g : B → C) (h : A → B), (f ∘ g) ∘ h = f ∘ (g ∘ h))
-- #check (comp_apply : (g ∘ f) x = g (f x))
-- #check (congrArg f₁ : x = y → f₁ x = f₁ y)
-- #check (congr_fun : f₁ = f₂ → ∀ x, f₁ x = f₂ x)
-- #check (funext : (∀ x, f₁ x = f₂ x) → f₁ = f₂)
-- #check (invFun_comp : Injective f' → invFun f' ∘ f' = id)
-- #check (id_comp f₁ : id ∘ f₁ = f₁)
