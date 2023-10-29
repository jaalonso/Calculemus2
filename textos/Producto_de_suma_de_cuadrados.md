---
Título: Si x e y son sumas de dos cuadrados, entonces xy también lo es
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(x\\) e \\(y\\) son sumas de dos cuadrados, entonces \\(xy\\) también lo es

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [CommRing α]
variable {x y : α}

-- (suma_de_cuadrados x) afirma que x se puede escribir como la suma
-- de dos cuadrados.
def suma_de_cuadrados (x : α) :=
  ∃ a b, x = a^2 + b^2

example
  (hx : suma_de_cuadrados x)
  (hy : suma_de_cuadrados y)
  : suma_de_cuadrados (x * y) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Puesto que \\(x\\) e \\(y\\) se pueden escribir como la suma de dos cuadrados, existen \\(a\\), \\(b\\) , \\(c\\) y \\(d\\) tales que
\\begin{align}
   x &= a² + b² \\\\
   y &= c² + d²
\\end{align}
Entonces,
\\begin{align}
   xy &= (a² + b²)(c² + d²) \\\\
      &= a²c² + b²d² + a²d² + b²c² \\\\
      &= a²c² - 2acbd + b²d² + a²d² + 2adbc + b²c² \\\\
      &= (ac - bd)² + (ad + bc)²
\\end{align}
Por tanto, \\(xy\\) es la suma de dos cuadrados.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable {α : Type _} [CommRing α]
variable {x y : α}

-- (suma_de_cuadrados x) afirma que x se puede escribir como la suma
-- de dos cuadrados.
def suma_de_cuadrados (x : α) :=
  ∃ a b, x = a^2 + b^2

-- 1ª demostración
example
  (hx : suma_de_cuadrados x)
  (hy : suma_de_cuadrados y)
  : suma_de_cuadrados (x * y) :=
by
  rcases hx with ⟨a, b, xeq : x = a^2 + b^2⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq : y = c^2 + d^2⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2 :=
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2) :=
                by rw [xeq, yeq]
       _ = a^2*c^2 + b^2*d^2 + a^2*d^2 + b^2*c^2 :=
                by ring
       _ = a^2*c^2 - 2*a*c*b*d + b^2*d^2 + a^2*d^2 + 2*a*d*b*c + b^2*c^2 :=
                by ring
       _ = (a*c - b*d)^2 + (a*d + b*c)^2 :=
                by ring
  have h2 : ∃ f, x * y = (a*c - b*d)^2 + f^2 :=
    Exists.intro (a*d + b*c) h1
  have h3 : ∃ e f, x * y = e^2 + f^2 :=
    Exists.intro (a*c - b*d) h2
  show suma_de_cuadrados (x * y)
  exact h3

-- 2ª demostración
example
  (hx : suma_de_cuadrados x)
  (hy : suma_de_cuadrados y)
  : suma_de_cuadrados (x * y) :=
by
  rcases hx with ⟨a, b, xeq : x = a^2 + b^2⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq : y = c^2 + d^2⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2 :=
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     := by rw [xeq, yeq]
       _ = (a*c - b*d)^2 + (a*d + b*c)^2 := by ring
  have h2 : ∃ e f, x * y = e^2 + f^2 :=
    by tauto
  show suma_de_cuadrados (x * y)
  exact h2

-- 3ª demostración
example
  (hx : suma_de_cuadrados x)
  (hy : suma_de_cuadrados y)
  : suma_de_cuadrados (x * y) :=
by
  rcases hx with ⟨a, b, xeq⟩
  -- a b : α
  -- xeq : x = a ^ 2 + b ^ 2
  rcases hy with ⟨c, d, yeq⟩
  -- c d : α
  -- yeq : y = c ^ 2 + d ^ 2
  rw [xeq, yeq]
  -- ⊢ suma_de_cuadrados ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
  use a*c - b*d, a*d + b*c
  -- ⊢ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
  --   = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2
  ring

-- 4ª demostración
example
  (hx : suma_de_cuadrados x)
  (hy : suma_de_cuadrados y)
  : suma_de_cuadrados (x * y) :=
by
  rcases hx with ⟨a, b, rfl⟩
  -- ⊢ suma_de_cuadrados ((a ^ 2 + b ^ 2) * y)
  rcases hy with ⟨c, d, rfl⟩
  -- ⊢ suma_de_cuadrados ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
  use a*c - b*d, a*d + b*c
  -- ⊢ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)
  --   = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2
  ring
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Producto_de_suma_de_cuadrados.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 30.</li>
</ul>
