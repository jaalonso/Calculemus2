---
Título: Si x, y, z ∈ ℕ, entonces x divide a yxz
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si $x, y, z ∈ ℕ$, entonces $x$ divide a $yxz$.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y z : ℕ)

example : x ∣ y * x * z :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Por la transitividad de la divisibilidad aplicada a las relaciones
\begin{align}
    x &\mid yx \\\\
   yx &\mid yxz
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (x y z : ℕ)

-- 1ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  have h1 : x ∣ y * x :=
    dvd_mul_left x y
  have h2 : (y * x) ∣ (y * x * z) :=
    dvd_mul_right (y * x) z
  show x ∣ y * x * z
  exact dvd_trans h1 h2

-- 2ª demostración
-- ===============

example : x ∣ y * x * z :=
dvd_trans (dvd_mul_left x y) (dvd_mul_right (y * x) z)

-- 3ª demostración
-- ===============

example : x ∣ y * x * z :=
by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left


-- Los lemas utilizados son:
#check (dvd_mul_left x y : x ∣ y * x)
#check (dvd_mul_right x y : x ∣ x * y)
#check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Divisibilidad_de_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 19.</li>
</ul>
