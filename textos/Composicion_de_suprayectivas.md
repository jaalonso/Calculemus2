---
Título: La composición de funciones suprayectivas es suprayectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que la composición de funciones suprayectivas es suprayectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Function
variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Supongamos que \\(f : A → B\\) y \\(g : B → C\\) son suprayectivas. Tenemosque demostrar que
\\[ (∀z ∈ C)(∃x ∈ A)[g(f(x)) = z] \\]
Sea \\(z ∈ C\\). Por ser \\(g\\) suprayectiva, existe un \\(y ∈ B\\) tal que
\\[ g(y) = z \\tag{1} \\]
Por ser \\(f\\) suprayectiva, existe un \\(x ∈ A\\) tal que
\\[ f(x) = y \\tag{2} \\]
Por tanto,
\\begin{align}
    g(f(x)) &= g(y)   &&\\text{[por (2)]} \\\\
            &= z      &&\\text{[por (1)]}
\\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
open Function
variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

-- 1ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  use x
  -- ⊢ (g ∘ f) x = z
  dsimp
  -- ⊢ g (f x) = z
  rw [hx]
  -- ⊢ g y = z
  exact hy

-- 2ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  use x
  -- ⊢ (g ∘ f) x = z
  dsimp
  -- ⊢ g (f x) = z
  rw [hx, hy]

-- 3ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  cases' hg z with y hy
  -- y : β
  -- hy : g y = z
  cases' hf y with x hx
  -- x : α
  -- hx : f x = y
  exact ⟨x, by dsimp ; rw [hx, hy]⟩

-- 4ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : γ
  -- ⊢ ∃ a, (g ∘ f) a = z
  rcases hg z with ⟨y, hy : g y = z⟩
  rcases hf y with ⟨x, hx : f x = y⟩
  exact ⟨x, by dsimp ; rw [hx, hy]⟩

-- 5ª demostración
example
  (hg : Surjective g)
  (hf : Surjective f)
  : Surjective (g ∘ f) :=
Surjective.comp hg hf

-- Lemas usados
-- ============

-- #check (Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f))
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Composicion_de_suprayectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 31.</li>
</ul>
