---
Título: Existen infinitos números primos
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que existen infinitos números primos.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
open Nat

example
  (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Se usarán los siguientes lemas de los números naturales, donde \(\text{Primo}(n)\) se verifica si \(n\) es primo y \(\text{minFac}(n)\) es el menor factor primo de \(n\).

\begin{align}
   &n ≠ 1 → \text{Primo}(\text{minFac}(n)) \tag{L1} \\
   &n! > 0                                 \tag{L2} \\
   &0 < k → n < k + n                      \tag{L3} \\
   &k < n → n ≠ k                          \tag{L4} \\
   &k ≱ n → k ≤ n                          \tag{L5} \\
   &0 < k → k ≤ n → k ∣ n!                 \tag{L6} \\
   &0 < \text{minFac}(n)                   \tag{L7} \\
   &k ∣ m → (k ∣ n ↔ k ∣ m + n)            \tag{L8} \\
   &\text{minFac}(n) ∣ n                   \tag{L9} \\
   &\text{Primo}(n) → ¬n ∣ 1               \tag{L10}
\end{align}

Sea \(p\) el menor factor primo de \(n! + 1\). Tenemos que demostrar que \(n ≤ p\) y que \(p\) es primo.

Para demostrar que \(p\) es primo, por el lema L1, basta demostrar que
\[ n! + 1 ≠ 1 \]
Su demostración es
\begin{align}
   &n ! > 0          &&\text{[por L2]} \\
   &⟹ n ! + 1 > 1   &&\text{[por L3]} \\
   &⟹ n ! + 1 ≠ 1   &&\text{[por L4]}
\end{align}

Para demostrar \(n ≤ p\), por el lema L5, basta demostrar que \(n ≱ p\). Su demostración es
\begin{align}
   &n ≥ p        \\
   &⟹ p ∣ n!    &&\text{[por L6 y L7]} \\
   &⟹ p | 1     &&\text{[por L8 y L9]} \\
   &⟹ Falso     &&\text{[por L10 y \(p\) es primo]}
\end{align}

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
open Nat

-- 1ª demostración
-- ===============

example
  (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p :=
by
  let p := minFac (n !  + 1)
  have h1 : Nat.Prime p := by
    apply minFac_prime
    -- ⊢ n ! + 1 ≠ 1
    have h3 : n ! > 0     := factorial_pos n
    have h4 : n ! + 1 > 1 := Nat.lt_add_of_pos_left h3
    show n ! + 1 ≠ 1
    exact Nat.ne_of_gt h4
  use p
  constructor
  . -- ⊢ n ≤ p
    apply le_of_not_ge
    -- ⊢ ¬n ≥ p
    intro h5
    -- h5 : n ≥ p
    -- ⊢ False
    have h6 : p ∣ n ! := dvd_factorial (minFac_pos _) h5
    have h7 : p ∣ 1   := (Nat.dvd_add_iff_right h6).mpr (minFac_dvd _)
    show False
    exact (Nat.Prime.not_dvd_one h1) h7
  . -- ⊢ Nat.Prime p
    exact h1
  done

-- 2ª demostración
-- ===============

example
  (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p :=
exists_infinite_primes n

-- Lemas usados
-- ============

-- variable (k m n : ℕ)
-- #check (Nat.Prime.not_dvd_one : Nat.Prime n → ¬n ∣ 1)
-- #check (Nat.dvd_add_iff_right : k ∣ m → (k ∣ n ↔ k ∣ m + n))
-- #check (Nat.dvd_one : n ∣ 1 ↔ n = 1)
-- #check (Nat.lt_add_of_pos_left : 0 < k → n < k + n)
-- #check (Nat.ne_of_gt : k < n → n ≠ k)
-- #check (dvd_factorial : 0 < k → k ≤ n → k ∣ n !)
-- #check (factorial_pos n: n ! > 0)
-- #check (le_of_not_ge : ¬k ≥ n → k ≤ n)
-- #check (minFac_dvd n : minFac n ∣ n)
-- #check (minFac_pos n : 0 < minFac n)
-- #check (minFac_prime : n ≠ 1 → Nat.Prime (minFac n))
</pre>

<h3>Demostraciones interactivas</h3>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Infinitud_de_primos.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.
