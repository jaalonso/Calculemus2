---
Título: ∀ a b c ∈ ℝ, (c * b) * a = b * (a * c)
Autor:  José A. Alonso
---

Demostrar con Lean4 que los números reales tienen la siguiente propiedad
<pre lang="text">
(c * b) * a = b * (a * c)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
by sorry
</pre>

<b>Soluciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]

-- 2ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a
    = (b * c) * a := by rw [mul_comm c b]
  _ = b * (c * a) := by rw [mul_assoc]
  _ = b * (a * c) := by rw [mul_comm c a]

-- 3ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by ring
</pre>

<b>Comentarios (obtenidos con ChatGPT)</b>

**Pregunta:** Comenta la siguiente demostración con Lean4
<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 1ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by
  rw [mul_comm c b]
  rw [mul_assoc]
  rw [mul_comm c a]
</pre>

**ChatGPT:**

La demostración presentada en Lean4 utiliza tácticas proporcionadas por el módulo Mathlib para demostrar una igualdad en el álgebra real. A continuación, se detalla cada paso de la demostración:

1. La demostración se realiza para cualquier a, b y c en el conjunto de los números reales (ℝ). Esto se especifica en la declaración `example (a b c : ℝ)`.

2. La meta a demostrar es `(c * b) * a = b * (a * c)`. El objetivo es demostrar que la multiplicación de los números reales cumple con la propiedad conmutativa y asociativa.

3. La táctica `rw [mul_comm c b]` se utiliza para reescribir la meta utilizando la propiedad de conmutatividad de la multiplicación en los números reales. Esta táctica reemplaza todas las ocurrencias de `(c * b)` en la meta con `(b * c)`.

4. Luego, se utiliza la táctica `rw [mul_assoc]` para reescribir la meta utilizando la propiedad de asociatividad de la multiplicación en los números reales. Esta táctica reorganiza los términos en la meta según la asociatividad de la multiplicación; es decir, cambia `(b * c) * a` por `b * (c * a)`

5. Finalmente, la táctica `rw [mul_comm c a]` se utiliza para reescribir la meta nuevamente utilizando la propiedad de conmutatividad de la multiplicación. Esto cambia la ocurrencia de `(a * c)` en la meta por `(c * a)`.

Al combinar estos pasos, se ha demostrado que `(c * b) * a = b * (a * c)` utilizando las propiedades de conmutatividad y asociatividad de la multiplicación en los números reales.

**Pregunta:** Comenta la siguiente demostración con Lean4
<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 2ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a
    = (b * c) * a := by rw [mul_comm c b]
  _ = b * (c * a) := by rw [mul_assoc]
  _ = b * (a * c) := by rw [mul_comm c a]
</pre>

**ChatGPT:** La segunda demostración presentada en Lean4 utiliza la táctica calc para demostrar la igualdad `(c * b) * a = b * (a * c)` en el álgebra real. A continuación, se detalla cada paso de la demostración:

1. La declaración `example (a b c : ℝ)` especifica que la demostración se realiza para cualquier a, b y c en el conjunto de los números reales (ℝ).

2. Se utiliza la táctica `calc` para iniciar la demostración. Esta táctica permite realizar una secuencia de pasos de razonamiento utilizando igualdades y desigualdades.

3. En la primera línea de la secuencia de razonamiento, se establece `(c * b) * a = (b * c) * a` utilizando la propiedad de conmutatividad de la multiplicación en los números reales. Esto se logra mediante la táctica `by rw [mul_comm c b]`, que reemplaza `(c * b)` por `(b * c)` en la expresión.

4. En la siguiente línea, se utiliza el símbolo `_` para indicar que se continúa la secuencia de razonamiento. Se establece `(b * c) * a = b * (c * a)` utilizando la propiedad de asociatividad de la multiplicación en los números reales. Esto se realiza mediante la táctica `by rw [mul_assoc]`, que reorganiza los términos en la expresión según la asociatividad de la multiplicación.

5. En la última línea, nuevamente se utiliza el símbolo `_` para continuar la secuencia de razonamiento. Se establece `b * (c * a) = b * (a * c)` utilizando la propiedad de conmutatividad de la multiplicación en los números reales. Esto se logra mediante la táctica `by rw [mul_comm c a]`, que reemplaza `(c * a)` por `(a * c)` en la expresión.

Al combinar estos pasos utilizando la táctica `calc`, se ha demostrado la igualdad `(c * b) * a = b * (a * c)` en el álgebra real. La táctica `calc` es útil para realizar demostraciones concisas y legibles al mostrar una secuencia de razonamiento paso a paso.

**Pregunta:** Comenta la siguiente demostración con Lean4
<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

-- 3ª demostración
example
  (a b c : ℝ)
  : (c * b) * a = b * (a * c) :=
by ring
</pre>

**ChatGPT:** La tercera demostración presentada en Lean4 utiliza la táctica `ring` para demostrar la igualdad `(c * b) * a = b * (a * c)` en el álgebra real.

La táctica `ring` es una táctica poderosa que se utiliza para demostrar igualdades en anillos, como el anillo de los números reales. Esta táctica se basa en propiedades algebraicas y simplificaciones automatizadas para probar igualdades.

En este caso, la demostración se realiza mediante una única línea de código: `by ring`. Al ejecutar esta táctica, Lean4 aplica automáticamente una secuencia de simplificaciones y propiedades algebraicas para demostrar la igualdad requerida. La táctica ring identifica la estructura de anillo de los números reales y aplica las propiedades de conmutatividad, asociatividad, distributividad y otros aspectos relevantes.

Dado que la táctica `ring` se encarga de todo el proceso de demostración de forma automática, no se requiere un análisis paso a paso adicional.

La utilización de la táctica `ring` es una forma conveniente y eficiente de demostrar igualdades algebraicas en anillos, pero es importante tener en cuenta que su aplicabilidad está limitada a casos donde se pueda inferir la estructura algebraica adecuada.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 5.
