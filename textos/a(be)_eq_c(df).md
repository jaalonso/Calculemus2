---
Título: Si ab = cd y e = f, entonces a(be) = c(df)
Autor:  José A. Alonso
---

Demostrar con Lean4 que si ab = cd y e = f, entonces a(be) = c(df)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  rw [h2]
  rw [←mul_assoc]
  rw [h1]
  rw [mul_assoc]

-- 2ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc
  a * (b * e)
    = a * (b * f) := by rw [h2]
  _ = (a * b) * f := by rw [←mul_assoc]
  _ = (c * d) * f := by rw [h1]
  _ = c * (d * f) := by rw [mul_assoc]

-- 3ª demostración
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by
  simp [*, ←mul_assoc]
</pre>

<b>Comentarios (a partir de los generados por ChatGPT)</b>

Las tres demostraciones presentadas tienen como objetivo demostrar la igualdad: `a * (b * e) = c * (d * f)`, utilizando las hipótesis `h1: a * b = c * d` y `h2: e = f`. A continuación, comentaré cada una de las demostraciones:

En la **1ª demostración** se utiliza el enfoque de reescribir (`rw`)  expresiones utilizando las igualdades dadas. El primer paso  reemplazar `e` por `f` usando la hipótesis `h2` (`rw [h2]`). Luego, se utiliza el lema de asociatividad de la multiplicación en sentido inverso (`←mul_assoc`) para reorganizar los términos y obtener `(a * b) * f = (c * d) * f`. Por último, se utiliza la hipótesis `h1` (`rw [h1`]) para reemplazar `a * b` por `c * d` y, finalmente,  usando la asociatividad se llega a la igualdad deseada.

En la **2ª demostración** se utiliza el enfoque de cálculo (`calc`) para realizar una secuencia de pasos de igualdad. Comienza con `a * (b * e)` y se utiliza la hipótesis `h2` para reemplazar `e` por `f` (`by rw [h2]`). Luego, se utiliza el lema de asociatividad de la multiplicación en sentido inverso (`←mul_assoc`) para reorganizar los términos y obtener `a * (b * f) = (a * b) * f`. A continuación, se utiliza la hipótesis `h1` para reemplazar `a * b` por `c * d` (`by rw [h1]`) y se obtiene `(c * d) * f`. Finalmente, se utiliza nuevamente el lema de asociatividad de la multiplicación en sentido directo (`mul_assoc`) para reorganizar los términos y obtener `c * (d * f)`, llegando así a la igualdad deseada.

En la **3ª demostración** se utiliza el enfoque de simplificación (`simp`). Se utiliza el modificador `*` para indicar que se deben utilizar todas las hipótesis y lemas disponibles. En este caso, se utiliza `*` y `←mul_assoc` para aplicar el lema de asociatividad de la multiplicación en sentido inverso. El objetivo es simplificar `a * (b * e)` a `c * (d * f)` directamente, aprovechando las igualdades `h1` y `h2`. Este enfoque permite simplificar la demostración a una sola línea.

En resumen, las tres demostraciones logran el mismo objetivo de demostrar la igualdad `a * (b * e) = c * (d * f)` utilizando diferentes enfoques. La primera utiliza reescrituras explícitas (`rw`), la segunda utiliza el enfoque de cálculo (`calc`) y la tercera utiliza la simplificación automática (`simp`). Cada enfoque tiene sus propias ventajas y puede ser preferido dependiendo del contexto y de la experiencia del desarrollador.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. ???.
