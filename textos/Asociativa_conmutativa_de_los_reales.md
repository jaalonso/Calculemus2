---
Título: Asociativa conmutativa de los reales.
Autor:  José A. Alonso
---

Demostrar con Lean4 que los números reales tienen la siguiente propiedad
<pre lang="text">
(a * b) * c = b * (a * c)
</pre>

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
sorry
</pre>

<b>Soluciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- 2ª demostración
example
  (a b c : ℝ)
  : (a * b) * c = b * (a * c) :=
calc
  (a * b) * c = (b * a) * c := by rw [mul_comm a b]
            _ = b * (a * c) := by rw [mul_assoc b a c]

-- 3ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
by ring
</pre>

<b>Comentarios (de ChatGPT)</b>

**Pregunta:** Comenta la siguiente demostración de Lean4
<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
</pre>

**ChatGPT:** La demostración presentada en Lean4 es un ejemplo de manipulación de expresiones algebraicas utilizando las tácticas de Lean.

En esta demostración se plantea el objetivo de demostrar la igualdad `(a * b) * c = b * (a * c)` para tres números reales `a`, `b` y `c`. La demostración comienza con la palabra clave `by`, lo que indica que se utilizarán tácticas para llegar a la conclusión.

La primera táctica utilizada es `rw [mul_comm a b]`, que aplica la regla de reescritura (`rw`) utilizando el lema `mul_comm` (multiplicación conmutativa) de la biblioteca Mathlib. Esta táctica intercambia el orden de los términos `a` y `b` en el primer término de la igualdad objetivo.

La segunda táctica es `rw [mul_assoc b a c]`, que utiliza la regla  reescritura (`rw`) con el lema `mul_assoc` (asociatividad de la multiplicación) de la biblioteca Mathlib. Esta táctica reorganiza los términos del primer término de la igualdad objetivo aplicando la asociatividad de la multiplicación; es decir, cambia `(b * a) * c` por `b * (a * c)`

Al aplicar estas dos tácticas, se llega a la igualdad objetivo deseada: `(a * b) * c = b * (a * c)`.

En resumen, la demostración utiliza las tácticas de reescritura para aplicar lemas algebraicos y manipular las expresiones en la igualdad hasta llegar a la forma deseada. Lean4 proporciona un entorno interactivo para construir demostraciones formales como esta utilizando tácticas y reglas predefinidas en sus bibliotecas matemáticas.

**Pregunta:** Comenta la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 2ª demostración
example
  (a b c : ℝ) : (a * b) * c = b * (a * c) :=
calc
(a * b) * c = (b * a) * c := by rw [mul_comm a b]
          _ = b * (a * c) := by rw [mul_assoc b a c]
</pre>

**ChatGPT:** La segunda demostración en Lean4 utiliza la táctica `calc`, que es una forma más compacta de realizar razonamientos matemáticos paso a paso.

La demostración comienza definiendo el objetivo de demostrar la igualdad `(a * b) * c = b * (a * c)` para los números reales `a`, `b` y `c`. Luego, se utiliza la táctica `calc` para realizar la cadena de razonamientos.

En la primera línea de la cadena, se utiliza `calc` seguido de `:=` para indicar que se va a realizar un razonamiento. Se establece `(a * b) * c = (b * a) * c` utilizando la regla de reescritura (`mul_comm a b`) que intercambia el orden de `a` y `b` en el primer término de la igualdad.

En la segunda línea de la cadena, se utiliza `_` para indicar que se desea completar la prueba. A continuación, se utiliza `:=` para establecer que se realizará otro razonamiento. Se utiliza la regla de reescritura (`mul_assoc b a c`) para reorganizar los términos en el segundo término de la igualdad y se llega a la conclusión `b * (a * c)`.

En resumen, la segunda demostración utiliza la táctica `calc` para realizar una cadena de razonamientos matemáticos paso a paso de manera más concisa. Se utilizan las reglas de reescritura `mul_comm` y `mul_assoc` para intercambiar y reorganizar los términos en la igualdad hasta llegar a la forma deseada.

**Pregunta:** Comenta la siguiente demostración en Lean4

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 3ª demostración
example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
by ring
</pre>

**ChatGPT:** La tercera demostración en Lean4 utiliza la táctica `ring` para demostrar la igualdad `(a * b) * c = b * (a * c)` de manera automática.

La táctica `ring` se basa en la teoría de los anillos y permite simplificar expresiones algebraicas utilizando propiedades y leyes de los anillos. En este caso, la táctica `ring` analiza la expresión y aplica las reglas de conmutatividad y asociatividad de la multiplicación para llegar a la igualdad deseada.

La demostración simplemente consiste en la palabra clave `by` seguida de `ring`. Esto indica que se desea utilizar la táctica `ring` para demostrar la igualdad. Al ejecutar la táctica `ring`, Lean4 simplifica la expresión `(a * b) * c` y la transforma en `b * (a * c)`, cumpliendo así con la igualdad establecida.

En resumen, la tercera demostración utiliza la táctica `ring` para realizar una simplificación automática de la expresión algebraica y demostrar la igualdad sin necesidad de manipulaciones manuales. Esta táctica es especialmente útil cuando se trabaja con estructuras algebraicas más complejas y puede ahorrar tiempo y esfuerzo en la demostración.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 5.
