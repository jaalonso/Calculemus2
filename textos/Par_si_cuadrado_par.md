---
Título: Si n² es par, entonces n es par.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \(n²\) es par, entonces \(n\) es par.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
open Nat
variable (n : ℕ)

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se usará el siguiente lema: Si \(p\) es primo, entonces
\[ (∀ a, b ∈ ℕ)[p ∣ ab ↔ p ∣ a ∨ p ∣ b] \]

Si \(n²\) es par, entonces \(2\) divide a \(n.n\) y, por el lema, \(2\) divide a \(n\).

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
open Nat
variable (n : ℕ)

-- 1ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h1 : Nat.Prime 2 := prime_two
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Prime.dvd_mul h1).mp h
  rcases h2 with h3 | h4
  · -- h3 : 2 ∣ n
    exact h3
  · -- h4 : 2 ∣ n
    exact h4
  done

-- 2ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Prime.dvd_mul prime_two).mp h
  rcases h2 with h3 | h4
  · exact h3
  · exact h4
  done

-- 3ª demostración
-- ===============

example
  (h : 2 ∣ n ^ 2)
  : 2 ∣ n :=
by
  rw [pow_two] at h
  -- h : 2 ∣ n * n
  have h2 : 2 ∣ n ∨ 2 ∣ n := (Prime.dvd_mul prime_two).mp h
  tauto
  done

-- Lemas usados
-- ============

-- variable (p a b : ℕ)
-- #check (prime_two : Nat.Prime 2)
-- #check (Prime.dvd_mul : Nat.Prime p → (p ∣ a * b ↔ p ∣ a ∨ p ∣ b))
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Par_si_cuadrado_par.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.
