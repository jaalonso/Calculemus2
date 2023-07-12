---
Título: El producto por un par es par.
Autor:  José A. Alonso
---

Demostrar que los productos de los números naturales por números pares son pares.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

example : ∀ m n : ℕ, Even n → Even (m * n) := by
  sorry
</pre>

<!-- more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 1ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring

-- 2ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  rw [mul_add]

-- 3ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk, mul_add]

-- 4ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk, mul_add]

-- 5ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  exact ⟨m * k, by rw [hk, mul_add]⟩

-- 6ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

-- 7ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  exact mul_add m k k

-- 8ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros m n hn
  unfold Even at *
  cases hn with
  | intro k hk =>
    use m * k
    rw [hk, mul_add]

-- 9ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros m n hn
  unfold Even at *
  cases hn with
  | intro k hk =>
    use m * k
    calc m * n
       = m * (k + k)   := by exact congrArg (HMul.hMul m) hk
     _ = m * k + m * k := by exact mul_add m k k

-- 10ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
</pre>

<b>Comentarios (con ChatGPT)</b>

**Pregunta:** Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 1ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring
</pre>

**ChatGPT:** La demostración en Lean4 muestra que para todo número natural `m` y `n`, si `n` es par, entonces `m * n` también es par.

La demostración comienza con el comando `example`, que establece la meta que se desea demostrar. Luego, se introducen las variables `m` y `n` utilizando el comando `rintro`, lo que permite utilizarlas en la prueba. A continuación, se introduce la hipótesis de que `n` es par utilizando `⟨k, hk⟩`, donde `k` es un número natural y `hk` es una prueba de que `n = k + k`.

Para demostrar que `m * n` es par, se utiliza el comando `use m * k`, que establece `m * k` como el número natural que demostrará que `m * n` es par. Luego, se utiliza el comando `rw [hk]` para reemplazar `n` en la meta con `k + k`, utilizando la prueba `hk`.

Finalmente, se utiliza el comando `ring` para simplificar la expresión `m * (k + k)` a `m * k + m * k` utilizando las propiedades algebraicas de los números naturales.

En resumen, la demostración establece que si `n` es par, entonces `m * n` también es par, utilizando la propiedad de la paridad de los números naturales.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 2ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  rw [mul_add]
</pre>

**ChatGPT:** La segunda demostración en Lean4 es similar a la primera, pero incluye un paso adicional utilizando el comando `rw [mul_add]`.

Al igual que en la primera demostración, se comienza con el comando `example`, se introducen las variables `m` y `n` con `rintro`, y se establece la hipótesis de que `n` es par utilizando `⟨k, hk⟩`. A continuación, se utiliza el comando `use m * k` para establecer `m * k` como el número natural que demostrará que `m * n` es par.

Después de eso, se utiliza el comando `rw [hk]` para reemplazar `n` en la meta por `k *+ k`, utilizando la prueba `hk`. Esto es similar a la primera demostración.

Sin embargo, en la segunda demostración se agrega el comando `rw [mul_add]` adicionalmente. Este comando utiliza la propiedad distributiva de la multiplicación respecto a la adición en los números naturales. Al aplicar `rw [mul_add]`, se expande la expresión `m * (k + k)` en la meta a `m * k + m * k`.

En resumen, la segunda demostración es una extensión de la primera, donde se agrega el paso adicional `rw [mul_add]` para aplicar la propiedad distributiva de la multiplicación respecto a la adición en los números naturales. Esto permite expandir la expresión `m * (k + k)` a `m * k + m * k` en la meta de la demostración.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 3ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk, mul_add]
</pre>

**ChatGPT** La tercera demostración comienza con el comando `rintro` seguido de `m n ⟨k, hk⟩`. Esto introduce las variables `m` y `n`, así como una hipótesis `hk` de la forma `⟨k, hk⟩` que establece que `n` es par.

Luego se utiliza `use m * k` para establecer `m * k` como el número  demostrará que `m * n` es par. Esto se logra al utilizar el comando `rw` (reemplazo) con `[hk, mul_add]`. El reemplazo se realiza en dos pasos. Primero, se reemplaza `hk`, lo que resulta en la sustitución de `n` por `k + k` en la meta. Luego, se aplica la propiedad distributiva de la multiplicación respecto a la adición en los números naturales, expandiendo la expresión `m * (k + k)` a `m * k + m * k`.

En resumen, la tercera demostración utiliza la introducción de variables, la asignación de un número específico (`m * k`) para demostrar la paridad de `m * n`, y luego realiza reemplazos para simplificar la expresión y llegar al resultado deseado.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 4ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk, mul_add]
</pre>

**ChatGPT:** La cuarta demostración utiliza una notación más compacta en comparación con las demostraciones anteriores. Comienza con el comando `rintro m n ⟨k, hk⟩`, que introduce las variables `m` y `n`, así como una hipótesis `hk` de la forma `⟨k, hk⟩` que establece que `n` es par.

Luego se utiliza `use m * k` para establecer `m * k` como el número que demostrará que `m * n` es par. Esta es una abreviatura de `use (m * k)`.

A continuación, se utiliza el comando `rw [hk, mul_add]` para realizar dos reemplazos en un solo paso. Primero, se reemplaza `hk`, lo que sustituye `n` por `k + k` en la meta. Luego, se aplica la propiedad distributiva de la multiplicación respecto a la adición en los números naturales, expandiendo la expresión `m * (k + k)` a `m * k + m * k`.

En resumen, la cuarta demostración utiliza una notación más compacta para introducir variables y establecer el número que demuestra la paridad de `m * n`, y luego realiza los reemplazos necesarios para simplificar la expresión y alcanzar el resultado deseado.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 5ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  exact ⟨m * k, by rw [hk, mul_add]⟩
</pre>

**ChatGPT:** La quinta demostración comienza con el comando `rintro` para introducir las variables `m` y `n`, y luego `⟨k, hk⟩` se utiliza para establecer la hipótesis de paridad `n = k + k`, donde `k` es un número natural y `hk` es una prueba de esta igualdad.

Luego se utiliza el comando `exact ⟨m * k, by rw [hk, mul_add]⟩` para establecer directamente `⟨m * k, …⟩` como la prueba requerida de que `m * n` es par. Aquí, `⟨m * k, …⟩` representa el número `m * k` como testigo de la paridad, y `by rw [hk, mul_add]` proporciona una prueba que muestra que ese número es par.

Dentro de `by rw [hk, mul_add]`, se realiza el reemplazo utilizando `rw`. Primero, se reemplaza `hk`, lo que sustituye `n` por `k + k` en la meta. Luego, se aplica la propiedad distributiva de la multiplicación respecto a la adición en los números naturales, expandiendo la expresión `m * (k + k)` a `m * k + m * k`.

En resumen, la quinta demostración utiliza el comando `rintro` para introducir las variables y la hipótesis de paridad, y luego utiliza `exact` para establecer directamente el número y la prueba requeridos para demostrar la paridad de `m * n`. Proporciona una solución directa y concisa al problema planteado.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 6ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
</pre>

**ChatGPT:** La sexta demostración utiliza una notación de función lambda para definir directamente la prueba requerida. Comienza con `fun m n ⟨k, hk⟩ ↦`, donde se introducen las variables `m` y `n`, y se establece una hipótesis `⟨k, hk⟩` que afirma que `n` es par.

Luego, se utiliza `⟨m * k, by rw [hk, mul_add]⟩` para establecer directamente `m * k` como el número que demostrará que `m * n` es par. Esto se hace mediante el uso de la notación `⟨valor, prueba⟩`, donde `valor` representa el número que se utilizará como testigo de la paridad y `prueba` es una prueba que muestra que ese valor es par.

En este caso, se establece `m * k` como el valor y se proporciona  prueba utilizando by `rw [hk, mul_add]`. Aquí, `rw [hk, mul_add]` realiza dos reemplazos en un solo paso. Primero, se reemplaza `hk`, lo que sustituye `n` por `k + k` en la meta. Luego, se aplica la propiedad distributiva de la multiplicación respecto a la adición en los números naturales, expandiendo la expresión `m * (k + k)` a `m * k + m * k`.

En resumen, la sexta demostración utiliza una función lambda para definir directamente el valor y la prueba necesarios para demostrar la paridad de `m * n`. Proporciona una solución concisa y directa al problema planteado, al igual que la quinta demostración.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 7ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  exact mul_add m k k
</pre>

**ChatGPT:** La séptima demostración comienza con el comando `rintro` para introducir las variables `m` y `n`, y luego `⟨k, hk⟩` se utiliza para establecer la hipótesis de paridad `n = k + k`, donde `k` es un número natural y `hk` es una prueba de esta igualdad.

A continuación, se utiliza `use m * k` para establecer `m * k` como el número que demostrará que `m * n` es par.

Luego se utiliza `rw [hk]` para reemplazar `n` en la meta por `k + k`, utilizando la prueba `hk`.

Finalmente, se utiliza `exact mul_add m k k` para establecer que `m * (k + k)` es igual a `m * k + m * k`. Esto se logra utilizando la propiedad distributiva de la multiplicación respecto a la adición en los números naturales.

En resumen, la séptima demostración utiliza los comandos `rintro`, `use`, `rw` y `exact` para introducir variables, establecer el número testigo, realizar reemplazos y proporcionar una prueba final que demuestra la paridad de `m * n`.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 8ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros m n hn
  unfold Even at *
  cases hn with
  | intro k hk =&gt;
    use m * k
    rw [hk, mul_add]
</pre>

**ChatGPT:** La octava demostración comienza con el comando `intros m n hn` para introducir las variables `m` y `n`, así como la hipótesis de paridad `hn`. Luego se utiliza `unfold Even at *` para desplegar la definición de paridad en todos los lugares relevantes.

A continuación, se utiliza `cases hn with | intro k hk =>` para realizar un análisis de casos sobre la hipótesis de paridad `hn`. En el caso en que `hn` se cumple y se puede demostrar que `n = k + k`, se introduce una nueva variable `k` y una prueba `hk` que establece esa igualdad.

Dentro de este caso, se utiliza `use m * k` para establecer `m * k` como el número que demostrará que `m * n` es par. Luego se utiliza `rw [hk, mul_add]` para realizar los reemplazos correspondientes.

En resumen, la octava demostración utiliza `intros` para introducir las variables `m`, `n` y la hipótesis de paridad `hn`. Luego se utiliza `unfold Even at *` para desplegar la definición de paridad en todos los lugares relevantes. A continuación, se realiza un análisis de casos sobre la hipótesis de paridad utilizando `cases`, y se introduce el número testigo utilizando `use`. Finalmente, se realiza el reemplazo utilizando `rw` para simplificar la expresión y demostrar la paridad de `m * n`.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 9ª demostración
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros m n hn
  unfold Even at *
  cases hn with
  | intro k hk =&gt;
    use m * k
    calc m * n
       = m * (k + k)   := by exact congrArg (HMul.hMul m) hk
     _ = m * k + m * k := by exact mul_add m k k
</pre>

**ChatGPT:** La novena demostración comienza con el comando `intros m n hn` para introducir las variables `m` y `n`, así como la hipótesis de paridad `hn`. Luego se utiliza `unfold Even at *` para desplegar la definición de paridad en todos los lugares relevantes.

A continuación, se utiliza `cases hn with | intro k hk =>` para realizar un análisis de casos sobre la hipótesis de paridad `hn`. En el caso en que hn se cumple y se puede demostrar que `n = k + k`, se introduce una nueva variable `k` y una prueba `hk` que establece esa igualdad.

Dentro de este caso, se utiliza `use m * k` para establecer `m * k` como el número que demostrará que `m * n` es par.

Luego, se utiliza `calc m * n = m * (k + k) := by exact congrArg (HMul.hMul m) hk` para realizar un razonamiento algebraico paso a paso. La igualdad se deriva aplicando el lema `congrArg` al valor `m` y la prueba `hk` para mostrar que la multiplicación preserva la igualdad. Esto establece que `m * n` es igual a `m * (k + k)`.

Finalmente, se utiliza `_ = m * k + m * k := by exact mul_add m k k` para aplicar el lema `mul_add` y establecer que `m * k + m * k` es igual a `m * (k + k)`. Esto se logra utilizando la propiedad distributiva de la multiplicación respecto a la adición en los números naturales.

En resumen, la novena demostración utiliza `intros` para introducir las variables `m`, `n` y la hipótesis de paridad `hn`. Luego se utiliza `unfold Even at *` para desplegar la definición de paridad en todos los lugares relevantes. A continuación, se realiza un análisis de casos sobre la hipótesis de paridad utilizando `cases`, se introduce el número testigo utilizando `use`, y se utiliza `calc` y `by` para realizar razonamientos algebraicos paso a paso y establecer la igualdad necesaria.

**Pregunta:**: Explica la siguiente demostración en Lean4
<pre lang="lean">
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

open Nat

-- 10ª demostración
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
</pre>

**ChatGPT:** La décima demostración en Lean4 utiliza una estrategia de simplificación (`simp`) con las expresiones `*`, `parity_simps`. El comando `intros` se utiliza para introducir las variables y se utiliza `;` para combinar múltiples comandos en una sola línea.

El `simp` se aplica a las expresiones `*` y `parity_simps`. La expresión `*` indica que se deben aplicar simplificaciones con el contexto y la meta, mientras que `parity_simps` indica que se deben aplicar simplificaciones específicas relacionadas con la paridad de los números naturales.

En resumen, la décima demostración utiliza `intros` para introducir las variablesy luego aplica el comando `simp` con `*`, `parity_simps` para realizar las simplificaciones necesarias en la expresión `m * n` y demostrar su paridad. Esta estrategia simplificada permite una demostración concisa y automática del resultado deseado.

<b>Referencias</b>

+ J. Avigad y P. Massot. [Mathematics in Lean](https://bit.ly/44d6BMo), p. 3.
