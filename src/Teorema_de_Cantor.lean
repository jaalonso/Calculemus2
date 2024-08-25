-- Teorema_de_Cantor.lean
-- Teorema de Cantor
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-mayo-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar el teorema de Cantor:
--    ∀ f : α → Set α, ¬Surjective f
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea f una función de α en el conjunto de los subconjuntos de
-- α. Tenemos que demostrar que f no es suprayectiva. Lo haresmos por
-- reducción al absurdo. Para ello, supongamos que f es suprayectiva y
-- consideremos el conjunto
--    S := {i ∈ α | i ∉ f(i)}                                        (1)
-- Entonces, tiene que existir un j ∈ α tal que
--   f(j) = S                                                        (2)
-- Se pueden dar dos casos: j ∈ S ó j ∉ S. Veamos que ambos son
-- imposibles.
--
-- Caso 1: Supongamos que j ∈ S. Entonces, por (1)
--    j ∉ f(j)
-- y, por (2),
--    j ∉ S
-- que es una contradicción.
--
-- Caso 2: Supongamos que j ∉ S. Entonces, por (1)
--    j ∈ f(j)
-- y, por (2),
--    j ∈ S
-- que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Set.Basic

open Function

variable {α : Type}

-- 1ª demostración
-- ===============

example : ∀ f : α → Set α, ¬Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  unfold Surjective at hf
  -- hf : ∀ (b : Set α), ∃ a, f a = b
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  by_cases h: j ∈ S
  . -- h : j ∈ S
    simp at h
    -- h : ¬j ∈ f j
    apply h
    -- ⊢ j ∈ f j
    rw [hj]
    -- ⊢ j ∈ S
    exact h
  . -- h : ¬j ∈ S
    apply h
    -- ⊢ j ∈ S
    rw [←hj] at h
    -- h : ¬j ∈ f j
    exact h

-- 2ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  by_cases h: j ∈ S
  . -- h : j ∈ S
    apply h
    -- ⊢ j ∈ f j
    rwa [hj]
  . -- h : ¬j ∈ S
    apply h
    rwa [←hj] at h

-- 3ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
by
  intros f hf
  -- f : α → Set α
  -- hf : Surjective f
  -- ⊢ False
  let S := {i | i ∉ f i}
  cases' hf S with j hj
  -- j : α
  -- hj : f j = S
  have h : (j ∈ S) = (j ∉ S) :=
    calc  (j ∈ S)
       = (j ∉ f j) := Set.mem_setOf_eq
     _ = (j ∉ S)   := congrArg (j ∉ .) hj
  exact iff_not_self (iff_of_eq h)

-- 4ª demostración
-- ===============

example : ∀ f : α → Set α, ¬ Surjective f :=
cantor_surjective

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (p : α → Prop)
-- variable (a b : Prop)
-- #check (Set.mem_setOf_eq : (x ∈ {y : α | p y}) = p x)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (iff_not_self : ¬(a ↔ ¬a))
-- #check (cantor_surjective : ∀ f : α → Set α, ¬ Surjective f)
