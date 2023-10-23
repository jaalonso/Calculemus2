---
Título: La suma de dos funciones acotadas superiormente también lo está
Autor:  José A. Alonso
---

Demostrar con Lean4 que la suma de dos funciones acotadas superiormente también lo está.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import src.Suma_de_cotas_superiores
variable {f g : ℝ → ℝ}

-- (acotadaSup f) afirma que f tiene cota superior.
def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]

Del ejercicio [La suma de una cota superior de f y una cota superior de g es una cota superior de f+g](https://bit.ly/3QauluK) usaremos la definición de cota superior
\\[ CotaSuperior f a : ∀ x, f x ≤ a \\]
y el lema
\\[ sumaCotaSup: FnUb f a → FnUb g b → FnUb (f + g) (a + b) \\]

Puesto que \\(f\\) está acotada superiormente, tiene una cota superior. Sea
\\(a\\) una de dichas cotas. Análogamentte, puesto que \\(g\\) está acotada
superiormente, tiene una cota superior. Sea \\(b\\) una de dichas
cotas. Por el lema sumaCotaSup, \\(a+b\\) es una cota superior de \\(f+g). Por
consiguiente, \\(f+g\\) está acotada superiormente.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import src.Suma_de_cotas_superiores
variable {f g : ℝ → ℝ}

-- (acotadaSup f) afirma que f tiene cota superior.
def acotadaSup (f : ℝ → ℝ) :=
  ∃ a, CotaSuperior f a

-- 1ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : CotaSuperior f a
  cases' hg with b hb
  -- b : ℝ
  -- hb : CotaSuperior g b
  have h1 : CotaSuperior (f + g) (a + b) :=
    sumaCotaSup ha hb
  have h2 : ∃ z, CotaSuperior (f+g) z :=
    Exists.intro (a + b) h1
  show acotadaSup (f + g)
  exact h2

-- 2ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  cases' hf with a ha
  -- a : ℝ
  -- ha : FnUb f a
  cases' hg with b hb
  -- b : ℝ
  -- hb : FnUb g b
  use a + b
  apply sumaCotaSup ha hb

-- 4ª demostración
example
  (hf : acotadaSup f)
  (hg : acotadaSup g)
  : acotadaSup (f + g) :=
by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨a + b, sumaCotaSup ha hb⟩

-- 5ª demostración
example :
  acotadaSup f → acotadaSup g → acotadaSup (f + g) :=
by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨a + b, sumaCotaSup ha hb⟩

-- 6ª demostración
example :
  acotadaSup f → acotadaSup g → acotadaSup (f + g) :=
fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, sumaCotaSup ha hb⟩

-- Lemas usados
-- ============

-- #variable (a b : ℝ)
-- #check (sumaCotaSup : CotaSuperior f a → CotaSuperior g b → CotaSuperior (f + g) (a + b))
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_de_funciones_acotadas_superiormente.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 29.</li>
</ul>
