---
title: Intersección con la imagen
date: 2024-04-23 06:00:00 UTC+02:00
category: 'Funciones'
has_math: true
---

[mathjax]

Demostrar con Lean4 que
\\[ f[s] ∩ v = f[s ∩ f⁻¹[v]] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemmos que demostrar que, para todo \\(y\\),
\\[ y ∈ f[s] ∩ v ↔ y ∈ f[s ∩ f⁻¹[v]] \\]
Lo haremos demostrando las dos implicaciones.

(⟹) Supongamos que \\(y ∈ f[s] ∩ v\\). Entonces,
\\begin{align}
   &y ∈ f[s] \\tag{1} \\\\
   &y ∈ v    \\tag{2}
\\end{align}
Por (1), existe un \\(x\\) tal que
\\begin{align}
   &x ∈ s    \\tag{3} \\\\
   &f(x) = y \\tag{4}
\\end{align}
De (2) y (4), se tiene que
\\[ f(x) ∈ v \\]
y, por tanto,
\\[ x ∈ f⁻¹[v] \\tag{5} \\]
De (3) y (5), se tiene que
\\[ x ∈ s ∩ f⁻¹[v] \\]
Por tanto,
\\[ f(x) ∈ f[s ∩ f⁻¹[v]] \\]
y, por (4),
\\[ y ∈ f[s ∩ f⁻¹[v]] \\]

(⟸) Supongamos que \\(y ∈ f[s ∩ f⁻¹[v]]\\). Entonces, existe un \\(x\\) tal que
\\begin{align}
   &x ∈ s ∩ f⁻¹[v] \\tag{6} \\\\
   &f(x) = y       \\tag{7}
\\end{align}
Por (6), se tiene que
\\begin{align}
   &x ∈ s       \\tag{8} \\\\
   &x ∈ f⁻¹[v]  \\tag{9}
\\end{align}
Por (8), se tiene que
\\[ f(x) ∈ f[s] \\]
y, por (7),
\\[ y ∈ f[s] \\tag{10} \\]
Por (9),
\\[ f(x) ∈ v \\]
y, por (7),
\\[ y ∈ v \\tag{11} \\]
Por (10) y (11),
\\[ y ∈ f[s] ∩ v \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (v : Set β)

-- 1ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    cases' hy with hyfs yv
    -- hyfs : y ∈ f '' s
    -- yv : y ∈ v
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    have h1 : f x ∈ v := by rwa [←fxy] at yv
    have h3 : x ∈ s ∩ f ⁻¹' v := mem_inter xs h1
    have h4 : f x ∈ f '' (s ∩ f ⁻¹' v) := mem_image_of_mem f h3
    show y ∈ f '' (s ∩ f ⁻¹' v)
    rwa [fxy] at h4
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y
    cases' hx with hx1 fxy
    -- hx1 : x ∈ s ∩ f ⁻¹' v
    -- fxy : f x = y
    cases' hx1 with xs xfv
    -- xs : x ∈ s
    -- xfv : x ∈ f ⁻¹' v
    have h5 : f x ∈ f '' s := mem_image_of_mem f xs
    have h6 : y ∈ f '' s := by rwa [fxy] at h5
    have h7 : f x ∈ v := mem_preimage.mp xfv
    have h8 : y ∈ v := by rwa [fxy] at h7
    show y ∈ f '' s ∩ v
    exact mem_inter h6 h8

-- 2ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    intro hy
    -- hy : y ∈ f '' s ∩ v
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    cases' hy with hyfs yv
    -- hyfs : y ∈ f '' s
    -- yv : y ∈ v
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' v)
    -- ⊢ y ∈ f '' s ∩ v
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ y ∈ f '' s
      use x
      -- ⊢ x ∈ s ∧ f x = y
      constructor
      . -- ⊢ x ∈ s
        exact hx.1.1
      . -- ⊢ f x = y
        exact hx.2
    . -- ⊢ y ∈ v
      cases' hx with hx1 fxy
      -- hx1 : x ∈ s ∩ f ⁻¹' v
      -- fxy : f x = y
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact hx1.2

-- 3ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' v
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' v
        rw [mem_preimage]
        -- ⊢ f x ∈ v
        rw [fxy]
        -- ⊢ y ∈ v
        exact yv
    . exact fxy
  . rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    constructor
    . -- ⊢ y ∈ f '' s
      use x, xs
      -- ⊢ f x = y
      exact fxy
    . -- ⊢ y ∈ v
      rw [←fxy]
      -- ⊢ f x ∈ v
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' v
      exact xv

-- 4ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  constructor
  . -- ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
    rintro ⟨⟨x, xs, fxy⟩, yv⟩
    -- yv : y ∈ v
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
    aesop
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
    rintro ⟨x, ⟨xs, xv⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xv : x ∈ f ⁻¹' v
    -- ⊢ y ∈ f '' s ∩ v
    aesop

-- 5ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by ext ; constructor <;> aesop

-- 6ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
(image_inter_preimage f s v).symm

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (a b : Set α)
-- #check (image_inter_preimage f s v : f '' (s ∩ f ⁻¹' v) = f '' s ∩ v)
-- #check (mem_image_of_mem  f : x ∈ a → f x ∈ f '' a)
-- #check (mem_inter : x ∈ a → x ∈ b → x ∈ a ∩ b)
-- #check (mem_preimage : x ∈ f ⁻¹' v ↔ f x ∈ v)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Interseccion_con_la_imagen_inversa.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Interseccion_con_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof (rule equalityI)
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof (rule subsetI)
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof (rule IntE)
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof (rule imageE)
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then have "f x ∈ v"
          using ‹y ∈ v› by (rule subst)
        then have "x ∈ f -` v"
          by (rule vimageI2)
        with ‹x ∈ s› have "x ∈ s ∩ f -` v"
          by (rule IntI)
        then have "f x ∈ f ` (s ∩ f -` v)"
          by (rule imageI)
        with ‹y = f x› show "y ∈ f ` (s ∩ f -` v)"
          by (rule ssubst)
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      have "y ∈ f ` s"
      proof -
        have "x ∈ s"
          using hx by (rule IntD1)
        then have "f x ∈ f ` s"
          by (rule imageI)
        with ‹y = f x› show "y ∈ f ` s"
          by (rule ssubst)
      qed
      moreover
      have "y ∈ v"
      proof -
        have "x ∈ f -` v"
          using hx by (rule IntD2)
        then have "f x ∈ v"
          by (rule vimageD)
        with ‹y = f x› show "y ∈ v"
          by (rule ssubst)
      qed
      ultimately show "y ∈ (f ` s) ∩ v"
        by (rule IntI)
    qed
  qed
qed

(* 2ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then have "f x ∈ v" using ‹y ∈ v› by simp
        then have "x ∈ f -` v" by simp
        with ‹x ∈ s› have "x ∈ s ∩ f -` v" by simp
        then have "f x ∈ f ` (s ∩ f -` v)" by simp
        with ‹y = f x› show "y ∈ f ` (s ∩ f -` v)" by simp
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      have "y ∈ f ` s"
      proof -
        have "x ∈ s" using hx by simp
        then have "f x ∈ f ` s" by simp
        with ‹y = f x› show "y ∈ f ` s" by simp
      qed
      moreover
      have "y ∈ v"
      proof -
        have "x ∈ f -` v" using hx by simp
        then have "f x ∈ v" by simp
        with ‹y = f x› show "y ∈ v" by simp
      qed
      ultimately show "y ∈ (f ` s) ∩ v" by simp
    qed
  qed
qed

(* 2ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then show "y ∈ f ` (s ∩ f -` v)"
          using ‹x ∈ s› ‹y ∈ v› by simp
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      then have "y ∈ f ` s" using ‹y = f x› by simp
      moreover
      have "y ∈ v" using hx ‹y = f x› by simp
      ultimately show "y ∈ (f ` s) ∩ v" by simp
    qed
  qed
qed

(* 4ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
  by auto

end
</pre>
