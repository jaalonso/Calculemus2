---
Título: Si a es una cota superior no negativa de f y b es es una cota superior de la función no negativa g, entonces ab es una cota superior de fg
Autor:  José A. Alonso
---

Sean \\(f\\) y \\(g\\) funciones de \\(ℝ\\) en \\(ℝ\\). Demostrar con Lean4 que si \\(a\\) es una cota superior no negativa de \\(f\\) y \\(b\\) es es una cota superior de la función no negativa \\(g\\), entonces \\(ab\\) es una cota superior de \\(fg\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usará el siguiente lema
\\[ \\{a ≤ b, c ≤ d, 0 ≤ c, 0 ≤ b\\} ⊢ ac ≤ bd \\tag{L1} \\]

Hay que demostrar que
\\[ (∀ x ∈ ℝ) [f(x)g(x) ≤ ab] \\tag{1} \\]
Para ello, sea \\(x ∈ R\\). Puesto que \\(a\\) es una cota superior de \\(f\\), se tiene que
\\[ f(x) ≤ a \\tag{2} \\]
puesto que \\(b\\) es una cota superior de \\(g\\), se tiene que
\\[ g(x) ≤ b \\tag{3} \\]
puesto que \\(g\\) es no negativa, se tiene que
\\[ 0 ≤ g(x) \\tag{4} \\]
y, puesto que \\(a\\) es no negativo, se tiene que
\\[ 0 ≤ a \\tag{5} \\]
De (2), (3), (4) y (5), por L1, se tiene que
\\[ f(x)g(x) ≤ ab \\]
que es lo que había que demostrar.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- (CotaSuperior f a) se verifica si a es una cota superior de f.
def CotaSuperior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- (CotaInferior f a) expresa que a es una cota inferior de f.
def CotaInferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ)
variable (a b : ℝ)

-- 1ª demostración
example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
by
  have h1 : ∀ x, f x * g x ≤ a * b
  { intro x
    have h2 : f x ≤ a := hfa x
    have h3 : g x ≤ b := hgb x
    have h4 : 0 ≤ g x := nng x
    show f x * g x ≤ a * b
    exact mul_le_mul h2 h3 h4 nna }
  show CotaSuperior (f * g) (a * b)
  exact h1

-- 2ª demostración
example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
by
  intro x
  dsimp
  apply mul_le_mul
  . apply hfa
  . apply hgb
  . apply nng
  . apply nna

-- 3ª demostración
example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
by
  intro x
  have h1:= hfa x
  have h2:= hgb x
  have h3:= nng x
  exact mul_le_mul h1 h2 h3 nna

-- 4ª demostración
example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
by
  intro x
  specialize hfa x
  specialize hgb x
  specialize nng x
  exact mul_le_mul hfa hgb nng nna

-- 5ª demostración
example
  (hfa : CotaSuperior f a)
  (hgb : CotaSuperior g b)
  (nng : CotaInferior g 0)
  (nna : 0 ≤ a)
  : CotaSuperior (f * g) (a * b) :=
λ x ↦ mul_le_mul (hfa x) (hgb x) (nng x) nna

-- Lemas usados
-- ============

-- variable (c d : ℝ)
-- #check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Cota_superior_del_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 25.</li>
</ul>
