---
Título: Si (m ∣ n ∧ m ≠ n), entonces (m ∣ n ∧ ¬(n ∣ m)).
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \(m ∣ n ∧ m ≠ n\), entonces \(m ∣ n ∧ ¬(n ∣ m)\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.GCD.Basic

variable {m n : ℕ}

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

La primera parte de la conclusión coincide con la primera de la hipótesis. Nos queda demostrar la segunda parte; es decir, que \(¬(n | m)\). Para ello, supongamos que \(n | m\). Entonces, por la propiedad antisimétrica de la divisibilidad y la primera parte de la hipótesis, se tiene que \(m = n\) en contradicción con la segunda parte de la hipótesis.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Nat.GCD.Basic

variable {m n : ℕ}

-- 1ª demostración
-- ===============

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
by
  constructor
  . show m ∣ n
    exact h.left
  . show ¬n ∣ m
    { intro (h1 : n ∣ m)
      have h2 : m = n := dvd_antisymm h.left h1
      show False
      exact h.right h2 }

-- 2ª demostración
-- ===============

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
by
  constructor
  . exact h.left
  . intro (h1 : n ∣ m)
    exact h.right (dvd_antisymm h.left h1)

-- 3ª demostración
-- ===============

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
⟨h.left, fun h1 ↦ h.right (dvd_antisymm h.left h1)⟩

-- 4ª demostración
-- ===============

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
by
  cases' h with h1 h2
  -- h1 : m ∣ n
  -- h2 : m ≠ n
  constructor
  . -- ⊢ m ∣ n
    exact h1
  . -- ⊢ ¬n ∣ m
    contrapose! h2
    -- h2 : n ∣ m
    -- ⊢ m = n
    apply dvd_antisymm h1 h2

-- 5ª demostración
-- ===============

example
  (h : m ∣ n ∧ m ≠ n)
  : m ∣ n ∧ ¬ n ∣ m :=
by
  rcases h with ⟨h1 : m ∣ n, h2 : m ≠ n⟩
  constructor
  . -- ⊢ m ∣ n
    exact h1
  . -- ⊢ ¬n ∣ m
    contrapose! h2
    -- h2 : n ∣ m
    -- ⊢ m = n
    apply dvd_antisymm h1 h2

-- Lemas usados
-- ============

-- #check (dvd_antisymm : m ∣ n → n ∣ m → m = n)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Uso_de_conjuncion.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 36.</li>
</ul>
