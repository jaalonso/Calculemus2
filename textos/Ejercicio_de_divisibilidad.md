---
Título: Si x divide a w, entonces también divide a y(xz)+x²+w²
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \(x\) divide a \(w\), entonces también divide a \(y(xz)+x^2+w^2\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (w x y z : ℕ)

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Por la divisibilidad de la suma basta probar que
\begin{align}
   x &\mid yxz \tag{1} \\
   x &\mid x^2 \tag{2} \\
   x &\mid w^2 \tag{3}
\end{align}

Para demostrar (1), por la divisibilidad del producto se tiene
\[   x \mid xz\]
y, de nuevo por la divisibilidad del producto,
\[   x \mid y(xz)\]

La propiedad (2) se tiene por la definición de cuadrado y la divisibilidad del producto.

La propiedad (3) se tiene por la definición de cuadrado, la hipótesis y la divisibilidad del producto.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
variable (w x y z : ℕ)

-- 1ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  have h1 : x ∣ x * z :=
    dvd_mul_right x z
  have h2 : x ∣ y * (x * z) :=
    dvd_mul_of_dvd_right h1 y
  have h3 : x ∣ x^2 := by
    apply dvd_mul_left
  have h4 : x ∣ w * w :=
    dvd_mul_of_dvd_left h w
  have h5 : x ∣ w^2 := by
    rwa [← pow_two w] at h4
  have h6 : x ∣ y * (x * z) + x^2 :=
    dvd_add h2 h3
  show x ∣ y * (x * z) + x^2 + w^2
  exact dvd_add h6 h5

-- 2ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  apply dvd_add
  { apply dvd_add
    { apply dvd_mul_of_dvd_right
      apply dvd_mul_right }
    { rw [pow_two]
      apply dvd_mul_right }}
  { rw [pow_two]
    apply dvd_mul_of_dvd_left h }

-- 3ª demostración
example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
by
  repeat' apply dvd_add
  { apply dvd_mul_of_dvd_right
    apply dvd_mul_right }
  { rw [pow_two]
    apply dvd_mul_right }
  { rw [pow_two]
    apply dvd_mul_of_dvd_left h }

-- Lemas usados
-- ============

-- #check (dvd_add : x ∣ y → x ∣ z → x ∣ y + z)
-- #check (dvd_mul_left x y : x ∣ y * x)
-- #check (dvd_mul_right x y : x ∣ x * y)
-- #check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
-- #check (dvd_mul_of_dvd_right : x ∣ y → ∀ (c : ℕ), x ∣ c * y)
-- #check (pow_two x : x ^ 2 = x * x)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Ejercicio_de_divisibilidad.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 19.</li>
</ul>
