---
Título: Si bc = ef, entonces ((ab)c)d = ((ae)f)d
Autor:  José A. Alonso
---

Demostrar con Lean4 que si bc = ef, entonces ((ab)c)d = ((ae)f)d.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1ª demostración
example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by
  rw [mul_assoc a]
  rw [h]
  rw [←mul_assoc a]

-- 2ª demostración
example
  (a b c d e f : ℝ)
  (h : b * c = e * f)
  : ((a * b) * c) * d = ((a * e) * f) * d :=
calc
  ((a * b) * c) * d
    = (a * (b * c)) * d := by rw [mul_assoc a]
  _ = (a * (e * f)) * d := by rw [h]
  _ = ((a * e) * f) * d := by rw [←mul_assoc a]
</pre>

<b>Comentarios (a partir de los generados por ChatGPT)</b>

En ambas demostraciones se busca probar que `((a * b) * c) * d` es igual a `((a * e) * f) * d`, utilizando la hipótesis `h : b * c = e * f`.

En la **1ª demostración** se utiliza el estilo de tácticas de Lean para aplicar las tácticas de reescritura (`rw`) y asociatividad (`mul_assoc`). La demostración se realiza de la siguiente manera:

1. Primero se aplica la táctica `rw` para reescribir el término `((a * b) * c) * d` como `(a * (b * c)) * d` utilizando la asociatividad de la multiplicación (`mul_assoc a`).
2. Luego se utiliza la hipótesis `h` para reemplazar `b * c` por `e * f` mediante la táctica `rw [h]`.
3. Finalmente, se aplica la táctica `rw [←mul_assoc a]` para reescribir el término `(a * (e * f)) * d` como `((a * e) * f) * d` utilizando la asociatividad de la multiplicación en sentido inverso.

Con estas tres reescrituras, se llega a la conclusión de que `((a * b) * c) * d` es igual `a ((a * e) * f) * d`, y por lo tanto se completa la demostración.

En la **2ª demostración** se utiliza el estilo de cálculo (`calc`) de Lean. La demostración se realiza de la siguiente manera:

1. Se comienza estableciendo el término `((a * b) * c) * d`.
2. Luego, utilizando la táctica `by rw [mul_assoc a]`, se reescribe `(a * b) * c` como `a * (b * c)` utilizando la asociatividad de la multiplicación.
3. Después, se utiliza la hipótesis `h` para reemplazar `b * c` por `e * f` mediante la táctica `by rw [h]`.
4. En la siguiente línea, se utiliza el símbolo `_` para indicar que se está continuando la igualdad desde la línea anterior.
5. A continuación, se utiliza la táctica by `rw [←mul_assoc a]` para reescribir `(a * (e * f)) * d` como `((a * e) * f) * d` utilizando la asociatividad de la multiplicación en sentido inverso.
6. Finalmente, se obtiene `((a * e) * f) * d`, que es el mismo resultado que `((a * b) * c) * d`.

En resumen, ambas demostraciones utilizan tácticas de reescritura y asociatividad para llegar a la conclusión deseada. La primera demostración utiliza la sintaxis de estilo táctico de Lean, mientras que la segunda utiliza la sintaxis de estilo de cálculo.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 6.
