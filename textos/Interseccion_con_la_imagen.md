---
Título: f[s] ∩ t = f[s ∩ f⁻¹[t]].
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que
\\[ f[s] ∩ t = f[s ∩ f⁻¹[t]] \\]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (t : Set β)

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Tenemos que demostrar que, para toda \\(y\\),
\\[ y ∈ f[s] ∩ t ↔ y ∈ f[s ∩ f⁻¹[t]] \\]
Lo haremos probando las dos implicaciones.

(⟹) Supongamos que \\(y ∈ f[s] ∩ t\\). Entonces, se tiene que
\\begin{align}
   &y ∈ f[s] \\tag{1} \\\\
   &y ∈ t    \\tag{2}
\\end{align}
Por (1), existe un \\(x\\) tal que
\\begin{align}
   &x ∈ s     \\tag{3} \\\\
   &f(x) = y  \\tag{4}
\\end{align}
Por (2) y (4),
\\[ f(x) ∈ t \\]
y, por tanto,
\\[ x ∈ f⁻¹[t] \\]
que, junto con (3), da
\\{ x ∈ s ∩ f⁻¹[t] \\]
y, por tanto,
\\[ f(x) ∈ f[s ∩ f⁻¹[t]] \\]
que, junto con (4), da
\\[ y ∈ f[s ∩ f⁻¹[t]] \\]

(⟸) Supongamos que \\(y ∈ f[s ∩ f⁻¹[t]]\\). Entonces, existe un \\(x\\) tal que
\\begin{align}
   &x ∈ s ∩ f⁻¹[t] \\tag{5} \\\\
   &f(x) = y       \\tag{6}
\\end{align}
Por (1), se tiene que
\\begin{align}
   &x ∈ s      \\tag{7} \\\\
   &x ∈ f⁻¹[t] \\tag{8}
\\end{align}
Por (7) se tiene que
\\[ f(x) ∈ f[s] \\]
y, junto con (6), se tiene que
\\[ y ∈ f[s] \\tag{9} \\]
Por (8), se tiene que
\\[ f(x) ∈ t \\]
y, junto con (6), se tiene que
\\[ y ∈ t \\tag{10} \\]
Por (9) y (19), se tiene que
\\[ y ∈ f[s] ∩ t \\]

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

variable {α β : Type _}
variable (f : α → β)
variable (s : Set α)
variable (t : Set β)

-- 1ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ t ↔ y ∈ f '' (s ∩ f ⁻¹' t)
  have h1 : y ∈ f '' s ∩ t → y ∈ f '' (s ∩ f ⁻¹' t) := by
    intro hy
    -- hy : y ∈ f '' s ∩ t
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t)
    have h1a : y ∈ f '' s := hy.1
    obtain ⟨x : α, hx: x ∈ s ∧ f x = y⟩ := h1a
    have h1b : x ∈ s := hx.1
    have h1c : f x = y := hx.2
    have h1d : y ∈ t := hy.2
    have h1e : f x ∈ t := by rwa [←h1c] at h1d
    have h1f : x ∈ s ∩ f ⁻¹' t := mem_inter h1b h1e
    have h1g : f x ∈ f '' (s ∩ f ⁻¹' t) := mem_image_of_mem f h1f
    show y ∈ f '' (s ∩ f ⁻¹' t)
    rwa [h1c] at h1g
  have h2 : y ∈ f '' (s ∩ f ⁻¹' t) → y ∈ f '' s ∩ t :=  by
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' t)
    -- ⊢ y ∈ f '' s ∩ t
    obtain ⟨x : α, hx : x ∈ s ∩ f ⁻¹' t ∧ f x = y⟩ := hy
    have h2a : x ∈ s := hx.1.1
    have h2b : f x ∈ f '' s := mem_image_of_mem f h2a
    have h2c : y ∈ f '' s := by rwa [hx.2] at h2b
    have h2d : x ∈ f ⁻¹' t := hx.1.2
    have h2e : f x ∈ t := mem_preimage.mp h2d
    have h2f : y ∈ t := by rwa [hx.2] at h2e
    show y ∈ f '' s ∩ t
    exact mem_inter h2c h2f
  show y ∈ f '' s ∩ t ↔ y ∈ f '' (s ∩ f ⁻¹' t)
  exact ⟨h1, h2⟩

-- 2ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ t ↔ y ∈ f '' (s ∩ f ⁻¹' t)
  constructor
  . -- ⊢ y ∈ f '' s ∩ t → y ∈ f '' (s ∩ f ⁻¹' t)
    intro hy
    -- hy : y ∈ f '' s ∩ t
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t)
    cases' hy with hyfs yt
    -- hyfs : y ∈ f '' s
    -- yt : y ∈ t
    cases' hyfs with x hx
    -- x : α
    -- hx : x ∈ s ∧ f x = y
    cases' hx with xs fxy
    -- xs : x ∈ s
    -- fxy : f x = y
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' t ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' t
        rw [mem_preimage]
        -- ⊢ f x ∈ t
        rw [fxy]
        -- ⊢ y ∈ t
        exact yt
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t) → y ∈ f '' s ∩ t
    intro hy
    -- hy : y ∈ f '' (s ∩ f ⁻¹' t)
    -- ⊢ y ∈ f '' s ∩ t
    cases' hy with x hx
    -- x : α
    -- hx : x ∈ s ∩ f ⁻¹' t ∧ f x = y
    constructor
    . -- ⊢ y ∈ f '' s
      use x
      -- ⊢ x ∈ s ∧ f x = y
      constructor
      . -- ⊢ x ∈ s
        exact hx.1.1
      . -- ⊢ f x = y
        exact hx.2
    . -- ⊢ y ∈ t
      cases' hx with hx1 fxy
      -- hx1 : x ∈ s ∩ f ⁻¹' t
      -- fxy : f x = y
      rw [←fxy]
      -- ⊢ f x ∈ t
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' t
      exact hx1.2

-- 3ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ t ↔ y ∈ f '' (s ∩ f ⁻¹' t)
  constructor
  . -- ⊢ y ∈ f '' s ∩ t → y ∈ f '' (s ∩ f ⁻¹' t)
    rintro ⟨⟨x, xs, fxy⟩, yt⟩
    -- yt : y ∈ t
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t)
    use x
    -- ⊢ x ∈ s ∩ f ⁻¹' t ∧ f x = y
    constructor
    . -- ⊢ x ∈ s ∩ f ⁻¹' t
      constructor
      . -- ⊢ x ∈ s
        exact xs
      . -- ⊢ x ∈ f ⁻¹' t
        rw [mem_preimage]
        -- ⊢ f x ∈ t
        rw [fxy]
        -- ⊢ y ∈ t
        exact yt
    . -- ⊢ f x = y
      exact fxy
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t) → y ∈ f '' s ∩ t
    rintro ⟨x, ⟨xs, xt⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xt : x ∈ f ⁻¹' t
    -- ⊢ y ∈ f '' s ∩ t
    constructor
    . -- ⊢ y ∈ f '' s
      use x, xs
      -- ⊢ f x = y
      exact fxy
    . -- ⊢ y ∈ t
      rw [←fxy]
      -- ⊢ f x ∈ t
      rw [←mem_preimage]
      -- ⊢ x ∈ f ⁻¹' t
      exact xt

-- 4ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by
  ext y
  -- y : β
  -- ⊢ y ∈ f '' s ∩ t ↔ y ∈ f '' (s ∩ f ⁻¹' t)
  constructor
  . -- ⊢ y ∈ f '' s ∩ t → y ∈ f '' (s ∩ f ⁻¹' t)
    rintro ⟨⟨x, xs, fxy⟩, yt⟩
    -- yt : y ∈ t
    -- x : α
    -- xs : x ∈ s
    -- fxy : f x = y
    -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t)
    aesop
  . -- ⊢ y ∈ f '' (s ∩ f ⁻¹' t) → y ∈ f '' s ∩ t
    rintro ⟨x, ⟨xs, xt⟩, fxy⟩
    -- x : α
    -- fxy : f x = y
    -- xs : x ∈ s
    -- xt : x ∈ f ⁻¹' t
    -- ⊢ y ∈ f '' s ∩ t
    aesop

-- 5ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
by ext ; constructor <;> aesop

-- 6ª demostración
-- ===============

example : (f '' s) ∩ t = f '' (s ∩ f ⁻¹' t) :=
(image_inter_preimage f s t).symm

-- Lemas usados
-- ============

-- variable (x : α)
-- variable (v : Set α)
-- #check (image_inter_preimage f s t : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t)
-- #check (mem_image_of_mem f : x ∈ s → f x ∈ f '' s)
-- #check (mem_inter : x ∈ s → x ∈ v → x ∈ s ∩ v)
-- #check (mem_preimage : x ∈ f ⁻¹' t ↔ f x ∈ t)
</pre>

Se puede interactuar con las demostraciones anteriores en
[Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Interseccion_con_la_imagen.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Interseccion_con_la_imagen
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

(* 3ª demostración *)

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
