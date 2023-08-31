---
Título: Conmutatividad del máximo común divisor
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(m, n \in \mathbb{N}\) son números naturales, entonces
\[\gcd(m, n) = \gcd(n, m)\]


Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (k m n : ℕ)

open Nat

example : gcd m n = gcd n m :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Es consecuencia del siguiente lema auxiliar
\[   (\forall x, y \in \mathbb{N})[\gcd(x,y) \mid \gcd(y,x)] \tag{1} \]
En efecto, sustituyendo en (1) \(x\) por \(m\) e \(y\) por \(n\), se tiene
\[   \gcd(m, n) \mid \gcd(n, m) \tag{2}\]
y, sustituyendo en (1) \(x\) por \(n\) e \(y\) por \(m\), se tiene
\[   \gcd(n, m) \mid \gcd(m, n) \tag{3} \]
Finalmente, aplicando la propiedad antisimétrica de la divisibilidad a (2) y (3), se tiene
\[   \gcd(m, n) = \gcd(n, m) \]

Para demostrar (1), por la definición del máximo común divisor, basta demostrar las siguientes relaciones
\begin{align}
   \gcd(m, n) &\mid n \\
   \gcd(m, n) &\mid m
\end{align}
y ambas se tienen por la definición del máximo común divisor.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (k m n : ℕ)

open Nat

-- 1ª demostración del lema auxiliar
lemma aux : gcd m n ∣ gcd n m :=
by
  have h1 : gcd m n ∣ n :=
    gcd_dvd_right m n
  have h2 : gcd m n ∣ m :=
    gcd_dvd_left m n
  show gcd m n ∣ gcd n m
  exact dvd_gcd h1 h2

-- 2ª demostración del lema auxiliar
example : gcd m n ∣ gcd n m :=
dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)

-- 1ª demostración
example : gcd m n = gcd n m :=
by
  have h1 : gcd m n ∣ gcd n m := aux m n
  have h2 : gcd n m ∣ gcd m n := aux n m
  show gcd m n = gcd n m
  exact _root_.dvd_antisymm h1 h2

-- 2ª demostración
example : gcd m n = gcd n m :=
by
  apply _root_.dvd_antisymm
  { exact aux m n }
  { exact aux n m }

-- 3ª demostración
example : gcd m n = gcd n m :=
_root_.dvd_antisymm (aux m n) (aux n m)

-- 4ª demostración
example : gcd m n = gcd n m :=
-- by apply?
gcd_comm m n

-- Lemas usados
-- ============

-- #check (_root_.dvd_antisymm : m ∣ n → n ∣ m → m = n)
-- #check (dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n)
-- #check (gcd_comm m n : gcd m n = gcd n m)
-- #check (gcd_dvd_left  m n: gcd m n ∣ m)
-- #check (gcd_dvd_right m n : gcd m n ∣ n)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Conmutatividad_del_gcd.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 19.</li>
</ul>
