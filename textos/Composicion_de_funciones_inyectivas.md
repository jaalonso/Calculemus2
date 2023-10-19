---
Título: La composición de funciones inyectivas es inyectiva
Autor:  José A. Alonso
---

Demostrar con Lean4 que la composición de funciones inyectivas es inyectiva.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

open Function

variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by sorry
</pre>
<!--more-->

<b>Demostraciones en lenguaje natural (LN)</b>

[mathjax]
<b>1ª demostración en LN</b>

Tenemos que demostrar que
\\[ (∀ x, y) [(g ∘ f)(x) = (g ∘ f)(y) → x = y] \\]
Sean \\(x, y\\) tales que
\\[ (g ∘ f)(x) = (g ∘ f)(y) \\]
Entonces, por la definición de la composición,
\\[ g(f(x)) = g(f(y)) \\]
y, ser \\(g\\) inyectiva,
\\[ f(x) = f(y) \\]
y, ser \\(f\\) inyectiva,
\\[ x = y \\]

<b>2ª demostración en LN</b>

Tenemos que demostrar que
\\[ (∀ x, y) [(g ∘ f)(x) = (g ∘ f)(y) → x = y] \\]
Sean \\(x, y\\) tales que
\\[ (g ∘ f)(x) = (g ∘ f)(y) \\tag{1} \\]
y tenemos que demostrar que
\\[ x = y \\tag{2} \\]
El objetivo (2), usando que \\(f\\) es inyectiva, se reduce a
\\[ f(x) = f(y) \\]
que, usando que \\(g\\) es inyectiva, se reduce a
\\[ g(f(x)) = g(f(y)) \\]
que, por la definición de la composición, coincide con (1).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

open Function

variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}

-- 1ª demostración (basada en la 1ª en LN)
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro (x : α) (y : α) (h1: (g ∘ f) x = (g ∘ f) y)
  have h2: g (f x) = g (f y) := h1
  have h3: f x = f y := hg h2
  show x = y
  exact hf h3

-- 2ª demostración
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro (x : α) (y : α) (h1: (g ∘ f) x = (g ∘ f) y)
  have h2: f x = f y := hg h1
  show x = y
  exact hf h2

-- 3ª demostración
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intro x y h
  exact hf (hg h)

-- 4ª demostración
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
fun _ _ h ↦ hf (hg h)

-- 5ª demostración (basada en la 2ª en LN)
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by
  intros x y h
  -- x y : α
  -- h : (g ∘ f) x = (g ∘ f) y
  apply hf
  -- ⊢ f x = f y
  apply hg
  -- ⊢ g (f x) = g (f y)
  apply h

-- 6ª demostración
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
-- by exact?
Injective.comp hg hf

-- 7ª demostración
example
  (hg : Injective g)
  (hf : Injective f) :
  Injective (g ∘ f) :=
by tauto

-- Lemas usados
-- ============

-- #check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Composicion_de_funciones_inyectivas.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 28.</li>
</ul>
