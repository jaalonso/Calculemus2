---
Título: (a + b)(a + b) = aa + 2ab + bb
Autor:  José A. Alonso
---

Demostrar con Lean4 que si a y b son números reales, entonces
<pre lang="text">
   (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b c : ℝ)

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
</pre>

<b>Comentarios (a partir de los generados por ChatGPT)</b>

En estas demostraciones en Lean 4, se busca demostrar la igualdad de la expresión `(a + b) * (a + b)` con `a * a + 2 * (a * b) + b * b`. A continuación, explicaré paso a paso cada demostración:

En la **1ª demostración** se utiliza la táctica `calc`, que permite realizar cálculos paso a paso de manera estructurada. La demostración comienza con el término izquierdo de la igualdad inicial `(a + b) * (a + b)` y luego utiliza varias reescrituras para transformar la expresión hasta llegar a la forma deseada `a * a + 2 * (a * b) + b * b`:

+ Primero, se utiliza la táctica `rw` (`rewrite`) para reescribir `(a + b) * (a + b)` como `(a + b) * a + (a + b) * b`, utilizando la propiedad distributiva de la multiplicación respecto a la suma (`mul_add`).
+ Luego, se utiliza nuevamente la táctica `rw` para reescribir la expresión anterior como `a * a + b * a + (a + b) * b`, utilizando la propiedad distributiva de la multiplicación respecto a la suma en ambos términos (`add_mul`).
+ A continuación, se reescribe nuevamente para agrupar los términos de la forma deseada: `a * a + b * a + (a * b + b * b)`.
+ Se aplica una reasociación utilizando la táctica `rw` y la propiedad de asociatividad de la suma (`←add_assoc`), de manera que los términos se agrupen de la siguiente manera: `a * a + (b * a + a * b) + b * b`.
+ A continuación, se utiliza la táctica `rw` para intercambiar el orden de la multiplicación `b * a` por `a * b` (`mul_comm b a`), de modo que se obtiene `a * a + (a * b + a * b) + b * b`.
+ Finalmente, se utiliza `←two_mul` para agrupar los términos de la forma deseada: `a * a + 2 * (a * b) + b * b`.

La demostración se completa y se obtiene la igualdad deseada.

En la **2ª demostración** se utiliza el comando `calc` nuevamente y  aplican los mismos pasos que en la primera demostración, pero se hace uso del lema `mul_add` y `add_mul` en una sola línea y análogamente con los cuatro siguientes que se agrupan de dos en dos en dos líneas.

En la **3ª demostración** se utiliza el comando `calc`, pero en lugar de utilizar los lemas, se utiliza el comando `by ring`. Este comando permite simplificar expresiones algebraicas automáticamente.

En la **4ª demostración** se utiliza el comando `by ring` de forma directa. Al utilizar `by ring`, Lean 4 expande y simplifica automáticamente la expresión `(a + b) * (a + b)` hasta obtener `a * a + 2 * (a * b) + b * b`.

En la **5ª demostración** demostración se utiliza el comando `by` seguido de múltiples comandos `rw` con los lemas `mul_add`, `add_mul`,`←add_assoc`, `add_assoc (a * a)`, `mul_comm b a` y `←two_mul` para reemplazar términos y obtener la expresión deseada `a * a + 2 * (a * b) + b * b`. Cada comando rw se aplica en orden secuencial para realizar las sustituciones necesarias.

La **6ª demostración** es similar a la 5ª demostración, pero en lugar de utilizar comandos rw por separado, se agrupan todos los lemas. Esto permite realizar todas las sustituciones necesarias de manera más concisa.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 7.
