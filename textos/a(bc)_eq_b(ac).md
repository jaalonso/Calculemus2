---
Título: ∀ a b c ∈ ℝ, a * (b * c) = b * (a * c)
Autor:  José A. Alonso
---

Demostrar con Lean4 que ∀ a b c ∈ ℝ, a * (b * c) = b * (a * c)

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
by sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
by
  rw [←mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- 2ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
calc
  a * (b * c)
    = (a * b) * c := by rw [←mul_assoc]
  _ = (b * a) * c := by rw [mul_comm a b]
  _ = b * (a * c) := by rw [mul_assoc]

-- 3ª demostración
example
  (a b c : ℝ) : a * (b * c) = b * (a * c) :=
by ring
</pre>

<b>Comentarios (con ChatGPT)</b>

Las tres demostraciones son formas diferentes de demostrar la igualdad `a * (b * c) = b * (a * c)`, donde `a`, `b` y `c` son números reales.

En la **1ª demostración**, se utilizan las tácticas de reescritura (`rw`) para manipular la expresión y llegar al resultado deseado. La demostración se realiza en un bloque `by`, lo que significa que todas las tácticas se aplican secuencialmente. Aquí se muestra el paso a paso:

1. Se utiliza la táctica `rw [←mul_assoc]` para reescribir la expresión `a * (b * c)` como `(a * b) * c`. Esto se hace utilizando la asociatividad de la multiplicación.
2. Luego, se utiliza `rw [mul_comm a b]` para reescribir la expresión `a * b` como `b * a`. Esto se hace utilizando la conmutatividad de la multiplicación.
3. Finalmente, se utiliza `rw [mul_assoc]` para reescribir la expresión `(b * a) * c` como `b * (a * c)`. Nuevamente, se aplica la asociatividad de la multiplicación.

Al seguir estos pasos, se llega a la igualdad deseada: `a * (b * c) = b * (a * c)`.

En la **2ª demostración**, se utiliza la táctica `calc` para realizar la demostración utilizando un estilo más conciso y estructurado. Aquí se muestra el paso a paso:

1. Se inicia con la expresión `a * (b * c)`.
2. Luego, se utiliza la táctica `by rw [←mul_assoc]` para reescribir la expresión como `(a * b) * c`. Esto se hace utilizando la asociatividad de la multiplicación.
3. A continuación, se utiliza la táctica `by rw [mul_comm a b]` para reescribir la expresión como `(b * a) * c`. Esto se hace utilizando la conmutatividad de la multiplicación.
4. Por último, se utiliza la táctica `by rw [mul_assoc]` para reescribir la expresión como `b * (a * c)`. Se aplica la asociatividad de la multiplicación nuevamente.

Al seguir estos pasos, se llega a la igualdad deseada: `a * (b * c) = b * (a * c)`.

En la **3ª demostración**, se utiliza la táctica `ring` para demostrar la igualdad. La táctica `ring` es una táctica poderosa que puede demostrar automáticamente muchas identidades algebraicas.

Al utilizar `by ring`, se le indica al sistema de demostración automática que pruebe la igualdad utilizando propiedades algebraicas. En este caso, el sistema reconoce automáticamente que se puede aplicar la conmutatividad y la asociatividad de la multiplicación para llegar al resultado deseado.

En resumen, las tres demostraciones utilizan diferentes tácticas y estilos para llegar a la igualdad `a * (b * c) = b * (a * c)`. La primera y segunda demostración utilizan las tácticas `rw` y `calc`, respectivamente, para reescribir la expresión paso a paso. La tercera demostración utiliza la táctica `ring` para demostrar automáticamente la igualdad utilizando propiedades algebraicas.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 6.
