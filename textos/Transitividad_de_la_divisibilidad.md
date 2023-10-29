---
Título: Transitividad de la divisibilidad
Autor:  José A. Alonso
---

Demostrar con Lean4 la transitividad de la divisibilidad.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {a b c : ℕ}

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Supongamos que \\(a | b\\) y \\(b | c\\). Entonces, existen \\(d\\) y \\(e\\) tales que
\\begin{align}
   b &= ad \\tag{1} \\\\
   c &= be \\tag{2}
\\end{align}
Por tanto,
\\begin{align}
   c &= be       &&\\text{[por (2)]} \\\\
     &= (ad)e    &&\\text{[por (1)]} \\\\
     &= a(de)
\\end{align}
Por consiguiente, \\(a | c\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

variable {a b c : ℕ}

-- 1ª demostración
example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divbc with ⟨e, ceq : c = b * e⟩
  have h1 : c = a * (d * e) :=
    calc c = b * e      := ceq
        _ = (a * d) * e := congrArg (. * e) beq
        _ = a * (d * e) := mul_assoc a d e
  show a ∣ c
  exact Dvd.intro (d * e) h1.symm

-- 2ª demostración
example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divab with ⟨d, beq : b = a * d⟩
  rcases divbc with ⟨e, ceq : c = b * e⟩
  use (d * e)
  -- ⊢ c = a * (d * e)
  rw [ceq, beq]
  -- ⊢ (a * d) * e = a * (d * e)
  exact mul_assoc a d e

-- 3ª demostración
example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  rcases divbc with ⟨e, rfl⟩
  -- ⊢ a ∣ b * e
  rcases divab with ⟨d, rfl⟩
  -- ⊢ a ∣ a * d * e
  use (d * e)
  -- ⊢ a * d * e = a * (d * e)
  ring

-- 4ª demostración
example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by
  cases' divab with d beq
  -- d : ℕ
  -- beq : b = a * d
  cases' divbc with e ceq
  -- e : ℕ
  -- ceq : c = b * e
  rw [ceq, beq]
  -- ⊢ a ∣ a * d * e
  use (d * e)
  -- ⊢ (a * d) * e = a * (d * e)
  exact mul_assoc a d e

-- 5ª demostración
example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
by exact dvd_trans divab divbc

-- Lemas usados
-- ============

-- #check (mul_assoc a b c : (a * b) * c = a * (b * c))
-- #check (Dvd.intro c : a * c = b → a ∣ b)
-- #check (dvd_trans : a ∣ b → b ∣ c → a ∣ c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Transitividad_de_la_divisibilidad.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 30.</li>
</ul>
