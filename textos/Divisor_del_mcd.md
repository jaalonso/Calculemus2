---
Título: 3 divide al máximo común divisor de 6 y 15.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que 3 divide al máximo común divisor de 6 y 15.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic

open Nat

example : 3 ∣ gcd 6 15 :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se usará el siguiente lema
\\[ (∀ k, m, n ∈ ℕ)[k ∣ \gcd(m, n) ↔ k ∣ m ∧ k ∣ n] \\]

Por el lema,
\\[ 3 ∣ \gcd(6, 15) \\]
se reduce a
\\[ 3 ∣ 6 ∧ 3 ∣ 15 \\]
que se verifican fácilmente.

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic

open Nat

-- 1ª demostración
-- ===============

example : 3 ∣ gcd 6 15 :=
by
  rw [dvd_gcd_iff]
  -- ⊢ 3 ∣ 6 ∧ 3 ∣ 15
  constructor
  . -- 3 ∣ 6
    norm_num
  . -- ⊢ 3 ∣ 15
    norm_num

-- 2ª demostración
-- ===============

example : 3 ∣ gcd 6 15 :=
by
  rw [dvd_gcd_iff]
  -- ⊢ 3 ∣ 6 ∧ 3 ∣ 15
  constructor <;> norm_num

-- Lemas usados
-- ============

-- variable (k m n : ℕ)
-- #check (dvd_gcd_iff : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Divisor_del_mcd.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 37.</li>
</ul>
