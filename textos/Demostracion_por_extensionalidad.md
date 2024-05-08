---
Título: Las funciones f(x,y) = (x + y)² y g(x,y) = x² + 2xy + y² son iguales
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que las funciones \\(f(x,y) = (x + y)²\\) y \\(g(x,y) = x² + 2xy + y\\)² son iguales.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import  Mathlib.Data.Real.Basic

example : (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2) :=
by sorry
</pre>
<!--more-->

<h2>1. Demostraciones con Lean4</h2>

<pre lang="lean">
import  Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example : (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2) :=
by
  ext u v
  -- u v : ℝ
  -- ⊢ (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2
  ring

-- Comentario: La táctica ext transforma las conclusiones de la forma
-- (fun x ↦ f x) = (fun x ↦ g x) en f x = g x.

-- 2ª demostración
-- ===============

example : (fun x y : ℝ ↦ (x + y)^2) = (fun x y : ℝ ↦ x^2 + 2*x*y + y^2) :=
by { ext ; ring }
</pre>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Demostracion_por_extensionalidad.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<h3>Referencias</h3>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 41.</li>
</ul>
