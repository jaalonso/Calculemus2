---
Título: El producto por un par es par.
Autor:  José A. Alonso
---

Demostrar que los productos de los números naturales por números pares
son pares.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.parity
import tactic

open nat

example : ∀ m n : ℕ, even n → even (m * n) :=
sorry
</pre>

<!-- more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.nat.parity
import tactic

open nat

-- 1ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  intros m n hn,
  unfold even at *,
  cases hn with k hk,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 2ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  intros m n hn,
  cases hn with k hk,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 3ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 4ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  rw hk,
  exact mul_add m k k,
end

-- 5ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  rw [hk, mul_add]
end

-- 6ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  exact ⟨m * k, by rw [hk, mul_add]⟩
end

-- 7ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩

-- 8ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
  assume m n ⟨k, (hk : n = k + k)⟩,
  have hmn : m * n = m * k + m * k,
    by rw [hk, mul_add],
  show ∃ l, m * n = l + l,
    from ⟨_, hmn⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/El_producto_por_un_par_es_par.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 2.
