---
Título: Existen números primos m y n tales que 4 < m < n < 10.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que existen números primos \\(m\\) y \\(n\\) tales que \\(4 < m < n < 10\\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

example :
  ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Basta considerar los números \\(5\\) y \\(7\\), ya que son primos y \\(4 < 5 < 7 < 10\\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

example :
  ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n :=
by
  use 5, 7
  norm_num
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Primos_intermedios.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 36.</li>
</ul>
