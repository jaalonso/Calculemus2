---
Título: Si a divide a b y a c, entonces divide a b+c
Autor:  José A. Alonso
---

Demostrar con Lean4 que si \\(a\\) divide a \\(b\\) y a \\(c\\), entonces divide a \\(b+c\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic

variable {a b c : ℕ}

example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Puesto que \\(a\\) divide a \\(b\\) y a \\(c\\), existen \\(d\\) y \\(e\\) tales que
\\begin{align}
   b &= ad \\tag{1} \\\\
   c &= ae \\tag{2}
\\end{align}
Por tanto,
\\begin{align}
   b + c &= ad + c     &&\\text{[por (1)]} \\\\
         &= ad + ae    &&\\text{[por (2)]} \\\\
         &= a(d + e)   &&\\text{[por la distributiva]}
\\end{align}
Por consiguiente, \\(a\\) divide a \\(b + c\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic

variable {a b c : ℕ}

-- 1ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases h1 with ⟨d, beq : b = a * d⟩
  rcases h2 with ⟨e, ceq: c = a * e⟩
  have h1 : b + c = a * (d + e) :=
    calc b + c
         = (a * d) + c       := congrArg (. + c) beq
       _ = (a * d) + (a * e) := congrArg ((a * d) + .) ceq
       _ = a * (d + e)       := by rw [← mul_add]
  show a ∣ (b + c)
  exact Dvd.intro (d + e) h1.symm

-- 2ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases h1 with ⟨d, beq : b = a * d⟩
  rcases h2 with ⟨e, ceq: c = a * e⟩
  have h1 : b + c = a * (d + e) := by linarith
  show a ∣ (b + c)
  exact Dvd.intro (d + e) h1.symm

-- 3ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases h1 with ⟨d, beq : b = a * d⟩
  rcases h2 with ⟨e, ceq: c = a * e⟩
  show a ∣ (b + c)
  exact Dvd.intro (d + e) (by linarith)

-- 4ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by
  cases' h1 with d beq
  -- d : ℕ
  -- beq : b = a * d
  cases' h2 with e ceq
  -- e : ℕ
  -- ceq : c = a * e
  rw [ceq, beq]
  -- ⊢ a ∣ a * d + a * e
  use (d + e)
  -- ⊢ a * d + a * e = a * (d + e)
  ring

-- 5ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
by
  rcases h1 with ⟨d, rfl⟩
  -- ⊢ a ∣ a * d + c
  rcases h2 with ⟨e, rfl⟩
  -- ⊢ a ∣ a * d + a * e
  use (d + e)
  -- ⊢ a * d + a * e = a * (d + e)
  ring

-- 6ª demostración
example
  (h1 : a ∣ b)
  (h2 : a ∣ c)
  : a ∣ (b + c) :=
dvd_add h1 h2

-- Lemas usados
-- ============

-- #check (Dvd.intro c : a * c = b → a ∣ b)
-- #check (dvd_add : a ∣ b →  a ∣ c → a ∣ (b + c))
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Suma_divisible.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 30.</li>
</ul>
