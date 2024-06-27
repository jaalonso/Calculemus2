---
title: La composición por la izquierda con una inyectiva es una operación inyectiva
date: 2024-06-27 06:00:00 UTC+02:00
category: Funciones
has_math: true
---

[mathjax]

Sean \\(f_1\\) y \\(f_2\\) funciones de \\(X\\) en \\(Y\\) y \\(g\\) una función de \\(Y\\) en \\(Z\\). Demostrar con Lean4 que si \\(g\\) es inyectiva y \\(g ∘ f_1 = g ∘ f_2\\), entonces \\(f_1 = f_2\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function

variable {X Y Z : Type _}
variable {f₁ f₂ : X → Y}
variable {g : Y → Z}

example
  (hg : Injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(x ∈ X\\). Tenemos que demostrar que
\\[ f_1(x) = f_2(x) \\]
Puesto que \\(g\\) es inyectiva, basta demostrar que
\\[ g(f_1(x)) = g(f_2(x)) \\]
que se demuestra mediante la siguiente cadena de igualdades
\\begin{align}
   g(f_1(x)) &= (g ∘ f_1)(x)    \\\\
            &= (g ∘ f_2)(x)    &&\\text{[porque \\(g ∘ f_1 = g ∘ f_2\\)]} \\\\
            &= g(f_2(x))
end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
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
calc f₁ = id ∘ f₁         := (left_id f₁).symm
 _ = (invFun g ∘ g) ∘ f₁  := congrArg (. ∘ f₁) (invFun_comp hg).symm
 _ = invFun g ∘ (g ∘ f₁)  := comp.assoc (invFun g) g f₁
 _ = invFun g ∘ (g ∘ f₂)  := congrArg (invFun g ∘ .) hgf
 _ = (invFun g ∘ g) ∘ f₂  := comp.assoc (invFun g) g f₂
 _ = id ∘ f₂              := congrArg (. ∘ f₂) (invFun_comp hg)
 _ = f₂                   := left_id f₂

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
-- #check (comp.assoc : ∀ (f : C → D) (g : B → C) (h : A → B), (f ∘ g) ∘ h = f ∘ (g ∘ h))
-- #check (comp_apply : (g ∘ f) x = g (f x))
-- #check (congrArg f₁ : x = y → f₁ x = f₁ y)
-- #check (congr_fun : f₁ = f₂ → ∀ x, f₁ x = f₂ x)
-- #check (funext : (∀ x, f₁ x = f₂ x) → f₁ = f₂)
-- #check (invFun_comp : Injective f' → invFun f' ∘ f' = id)
-- #check (left_id f₁ : id ∘ f₁ = f₁)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva
imports Main
begin

(* 1ª demostración *)

lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof (rule ext)
  fix x
  have "(g ∘ f1) x = (g ∘ f2) x"
    using ‹g ∘ f1 = g ∘ f2› by (rule fun_cong)
  then have "g (f1 x) = g (f2 x)"
    by (simp only: o_apply)
  then show "f1 x = f2 x"
    using ‹inj g› by (simp only: injD)
qed

(* 2ª demostración *)

lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof
  fix x
  have "(g ∘ f1) x = (g ∘ f2) x"
    using ‹g ∘ f1 = g ∘ f2› by simp
  then have "g (f1 x) = g (f2 x)"
    by simp
  then show "f1 x = f2 x"
    using ‹inj g› by (simp only: injD)
qed

(* 3ª demostración *)

lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
using assms
by (metis fun.inj_map_strong inj_eq)

(* 4ª demostración *)

lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof -
  have "f1 = id ∘ f1"
    by (rule id_o [symmetric])
  also have "… = (inv g ∘ g) ∘ f1"
    by (simp add: assms(1))
  also have "… = inv g ∘ (g ∘ f1)"
    by (simp add: comp_assoc)
  also have "… = inv g ∘ (g ∘ f2)"
    using assms(2) by (rule arg_cong)
  also have "… = (inv g ∘ g) ∘ f2"
    by (simp add: comp_assoc)
  also have "… = id ∘ f2"
    by (simp add: assms(1))
  also have "… = f2"
    by (rule id_o)
  finally show "f1 = f2"
    by this
qed

(* 5ª demostración *)

lemma
  assumes "inj g"
          "g ∘ f1 = g ∘ f2"
  shows   "f1 = f2"
proof -
  have "f1 = (inv g ∘ g) ∘ f1"
    by (simp add: assms(1))
  also have "… = (inv g ∘ g) ∘ f2"
    using assms(2) by (simp add: comp_assoc)
  also have "… = f2"
    using assms(1) by simp
  finally show "f1 = f2" .
qed

end
</pre>
