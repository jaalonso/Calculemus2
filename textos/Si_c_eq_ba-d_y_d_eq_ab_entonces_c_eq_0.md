---
Título: Si c = ba-d y d = ab, entonces c = 0
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a, b, c y d son números reales tales
<pre lang="text">
   c = b * a - d
   d = a * b
</pre>
entonces
<pre lang="text">
   c = 0
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
by sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
by
  rw [h1]
  rw [mul_comm]
  rw [h2]
  rw [sub_self]

-- 2ª demostración
example
  (a b c d : ℝ)
  (h1 : c = b * a - d)
  (h2 : d = a * b)
  : c = 0 :=
calc
  c = b * a - d     := by rw [h1]
  _ = a * b - d     := by rw [mul_comm]
  _ = a * b - a * b := by rw [h2]
  _ = 0             := by rw [sub_self]
</pre>

<b>Comentarios (a partir de los generados por ChatGPT)</b>

En ambas demostraciones se busca probar que `c` es igual a `0`, utilizando las hipótesis `h1` y `h2` que establecen ciertas relaciones entre las variables `a`, `b`, `c` y `d`.

La **primera demostración** utiliza el enfoque de reescribir (`rw`) las expresiones para llegar al resultado deseado. Veamos cada paso en detalle:

+ En el primer paso, se utiliza la hipótesis `h1` para reemplazar `c` por `b * a - d`.
+ En el segundo paso, se utiliza la propiedad conmutativa de la multiplicación (`mul_comm`) para intercambiar el orden de multiplicación entre `b` y `a`.
+ En el tercer paso, se utiliza la hipótesis h2 para reemplazar `d` por `a * b`.
+ En el último paso, se utiliza la propiedad de la resta de un número consigo mismo (`sub_self`) para establecer que `a * b - a * b` es igual a `0`.

En conclusión, cada paso de reescritura se utiliza para simplificar la expresión original y llegar al resultado deseado de `c = 0`.

La **segunda demostración** utiliza el enfoque de cálculo (`calc`) para mostrar una secuencia de igualdades que llevan al resultado deseado. Veamos cada paso en detalle:

+ En el primer paso, se utiliza la hipótesis `h1` para establecer que `c` es igual a `b * a - d`.
+ En el segundo paso, se utiliza la propiedad conmutativa de la multiplicación (`mul_comm`) para intercambiar el orden de multiplicación entre `b` y `a`.
+ En el tercer paso, se utiliza la hipótesis `h2` para establecer que `a * b - d` es igual a `a * b - a * b`.
+ En el último paso, se utiliza la propiedad de la resta de un número consigo mismo (`sub_self`) para establecer que `a * b - a * b` es igual a `0`.

En resumen, la demostración utiliza el razonamiento transitivo para establecer una secuencia de igualdades que demuestran que `c` es igual a `0`.

Ambas demostraciones son válidas y alcanzan el mismo resultado final de `c = 0`. La elección entre utilizar reescritura o cálculo depende del estilo de razonamiento preferido y de la comodidad del matemático o programador que realiza la demostración.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 7.
