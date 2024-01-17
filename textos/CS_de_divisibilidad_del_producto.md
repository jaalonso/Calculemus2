---
Título: Si m divide a n o a k, entonces m divide a nk.
Autor:  José A. Alonso
---

[mathjax]

Demostrar con Lean4 que si \(m\) divide a \(n\) o a \(k\), entonces \(m\) divide a \(nk\).

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Tactic
variable {m n k : ℕ}

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

Se demuestra por casos.

Caso 1: Supongamos que \(m ∣ n\). Entonces, existe un \(a ∈ ℕ\) tal que
\[ n = ma \]
Por tanto,
\begin{align}
   nk &= (ma)k \\
      &= m(ak)
\end{align}
que es divisible por \(m\).

Caso 2: Supongamos que \(m ∣ k). Entonces, existe un \(b ∈ ℕ\) tal que
\[ k = mb \]
Por tanto,
\begin{align}
   nk &= n(mb) \\
      &= m(nb)
\end{align}
que es divisible por \(m\).

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Tactic
variable {m n k : ℕ}

-- 1ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    rcases h1 with ⟨a, ha⟩
    -- a : ℕ
    -- ha : n = m * a
    rw [ha]
    -- ⊢ m ∣ (m * a) * k
    rw [mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- h2 : m ∣ k
    rcases h2 with ⟨b, hb⟩
    -- b : ℕ
    -- hb : k = m * b
    rw [hb]
    -- ⊢ m ∣ n * (m * b)
    rw [mul_comm]
    -- ⊢ m ∣ (m * b) * n
    rw [mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 2ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    rcases h1 with ⟨a, ha⟩
    -- a : ℕ
    -- ha : n = m * a
    rw [ha, mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- h2 : m ∣ k
    rcases h2 with ⟨b, hb⟩
    -- b : ℕ
    -- hb : k = m * b
    rw [hb, mul_comm, mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 3ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  . -- a : ℕ
    -- ⊢ m ∣ (m * a) * k
    rw [mul_assoc]
    -- ⊢ m ∣ m * (a * k)
    exact dvd_mul_right m (a * k)
  . -- ⊢ m ∣ n * (m * b)
    rw [mul_comm, mul_assoc]
    -- ⊢ m ∣ m * (b * n)
    exact dvd_mul_right m (b * n)

-- 4ª demostración
-- ===============

example
  (h : m ∣ n ∨ m ∣ k)
  : m ∣ n * k :=
by
  rcases h with h1 | h2
  . -- h1 : m ∣ n
    exact dvd_mul_of_dvd_left h1 k
  . -- h2 : m ∣ k
    exact dvd_mul_of_dvd_right h2 n

-- Lemas usados
-- ============

-- #check (dvd_mul_of_dvd_left : m ∣ n → ∀ (c : ℕ), m ∣ n * c)
-- #check (dvd_mul_of_dvd_right : m ∣ n → ∀ (c : ℕ), m ∣ c * n)
-- #check (dvd_mul_right m n : m ∣ m * n)
-- #check (mul_assoc m n k : m * n * k = m * (n * k))
-- #check (mul_comm m n : m * n = n * m)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/CS_de_divisibilidad_del_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 39.</li>
</ul>

<b>Demostraciones con Isabelle/HOL</b>

<pre lang="isar">
theory CS_de_divisibilidad_del_producto
  imports Main
begin

(* 1ª demostración *)
lemma
  fixes n m k :: nat
  assumes "m dvd n ∨ m dvd k"
  shows "m dvd (n * k)"
using assms
proof
    assume "m dvd n"
    then obtain a where "n = m * a" by auto
    then have "n * k = m * (a * k)" by simp
    then show ?thesis by auto
  next
    assume "m dvd k"
    then obtain b where "k = m * b" by auto
    then have "n * k = m * (n * b)" by simp
    then show ?thesis by auto
qed

(* 2ª demostración *)
lemma
  fixes n m k :: nat
  assumes "m dvd n ∨ m dvd k"
  shows "m dvd (n * k)"
  using assms by auto

end
</pre>
