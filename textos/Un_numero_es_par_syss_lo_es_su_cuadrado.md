---
title: Un número es par si y solo si lo es su cuadrado
date: 2024-05-27 06:00:00 UTC+02:00
category: Divisibilidad
has_math: true
---

[mathjax]

Demostrar con Lean4 que un número es par si y solo si lo es su cuadrado.

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Int.Parity
import Mathlib.Tactic
open Int

variable (n : ℤ)

example :
  Even (n^2) ↔ Even n :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

Sea \\(n ∈ ℤ\\). Tenemos que demostrar que \\(n^2\\) es par si y solo si n es par. Lo haremos probando las dos implicaciones.

(⟹) Lo demostraremos por contraposición. Para ello, supongamos que \\(n\\) no es par. Entonces, existe un \\(k ∈ Z\\) tal que
\\[ n = 2k+1 \\tag{1} \\]
Luego,
\\begin{align}
   n^2 &= (2k+1)^2          &&\\text{[por (1)]} \\\\
       &= 4k^2+4k+1         \\\\
       &= 2(2k(k+1))+1
\\end{align}
Por tanto, \\(n^2\\) es impar.

(⟸) Supongamos que \\(n\\) es par. Entonces, existe un \\(k ∈ ℤ\\) tal que
\\[ n = 2k \\tag{2} \\]
Luego,
\\begin{align}
   n^2 &= (2k)^2          &&\\text{[por (2)]} \\\\
       &= 2(2k^2)
\\end{align}
Por tanto, \\(n^2\\) es par.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
import Mathlib.Data.Int.Parity
import Mathlib.Tactic
open Int

variable (n : ℤ)

-- 1ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    intro h
    -- h : ¬Even n
    -- ⊢ ¬Even (n ^ 2)
    rw [←odd_iff_not_even] at *
    -- h : Odd n
    -- ⊢ Odd (n ^ 2)
    cases' h with k hk
    -- k : ℤ
    -- hk : n = 2 * k + 1
    use 2*k*(k+1)
    -- ⊢ n ^ 2 = 2 * (2 * k * (k + 1)) + 1
    calc n^2
         = (2*k+1)^2       := by rw [hk]
       _ = 4*k^2+4*k+1     := by ring
       _ = 2*(2*k*(k+1))+1 := by ring
  . -- ⊢ Even n → Even (n ^ 2)
    intro h
    -- h : Even n
    -- ⊢ Even (n ^ 2)
    cases' h with k hk
    -- k : ℤ
    -- hk : n = k + k
    use 2*k^2
    -- ⊢ n ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    calc n^2
         = (k + k)^2     := by rw [hk]
       _ = 2*k^2 + 2*k^2 := by ring

-- 2ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    rw [←odd_iff_not_even]
    -- ⊢ Odd n → ¬Even (n ^ 2)
    rw [←odd_iff_not_even]
    -- ⊢ Odd n → Odd (n ^ 2)
    unfold Odd
    -- ⊢ (∃ k, n = 2 * k + 1) → ∃ k, n ^ 2 = 2 * k + 1
    intro h
    -- h : ∃ k, n = 2 * k + 1
    -- ⊢ ∃ k, n ^ 2 = 2 * k + 1
    cases' h with k hk
    -- k : ℤ
    -- hk : n = 2 * k + 1
    use 2*k*(k+1)
    -- ⊢ n ^ 2 = 2 * (2 * k * (k + 1)) + 1
    rw [hk]
    -- ⊢ (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1
    ring
  . -- ⊢ Even n → Even (n ^ 2)
    unfold Even
    -- ⊢ (∃ r, n = r + r) → ∃ r, n ^ 2 = r + r
    intro h
    -- h : ∃ r, n = r + r
    -- ⊢ ∃ r, n ^ 2 = r + r
    cases' h with k hk
    -- k : ℤ
    -- hk : n = k + k
    use 2*k^2
    -- ⊢ n ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    rw [hk]
    -- ⊢ (k + k) ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    ring

-- 3ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
by
  constructor
  . -- ⊢ Even (n ^ 2) → Even n
    contrapose
    -- ⊢ ¬Even n → ¬Even (n ^ 2)
    rw [←odd_iff_not_even]
    -- ⊢ Odd n → ¬Even (n ^ 2)
    rw [←odd_iff_not_even]
    -- ⊢ Odd n → Odd (n ^ 2)
    rintro ⟨k, rfl⟩
    -- k : ℤ
    -- ⊢ Odd ((2 * k + 1) ^ 2)
    use 2*k*(k+1)
    -- ⊢ (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1
    ring
  . -- ⊢ Even n → Even (n ^ 2)
    rintro ⟨k, rfl⟩
    -- k : ℤ
    -- ⊢ Even ((k + k) ^ 2)
    use 2*k^2
    -- ⊢ (k + k) ^ 2 = 2 * k ^ 2 + 2 * k ^ 2
    ring

-- 4ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
calc Even (n^2)
     ↔ Even (n * n)      := iff_of_eq (congrArg Even (sq n))
   _ ↔ (Even n ∨ Even n) := even_mul
   _ ↔ Even n            := or_self_iff (Even n)

-- 5ª demostración
-- ===============

example :
  Even (n^2) ↔ Even n :=
calc Even (n^2)
     ↔ Even (n * n)      := by ring_nf
   _ ↔ (Even n ∨ Even n) := even_mul
   _ ↔ Even n            := by simp

-- Lemas usados
-- ============

-- variable (a b : Prop)
-- variable (m : ℤ)
-- #check (even_mul : Even (m * n) ↔ Even m ∨ Even n)
-- #check (iff_of_eq : a = b → (a ↔ b))
-- #check (odd_iff_not_even : Odd n ↔ ¬Even n)
-- #check (or_self_iff a : a ∨ a ↔ a)
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Un_numero_es_par_syss_lo_es_su_cuadrado).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory Un_numero_es_par_syss_lo_es_su_cuadrado
imports Main
begin

(* 1ª demostración *)

lemma
  fixes n :: int
  shows "even (n⇧2) ⟷ even n"
proof (rule iffI)
  assume "even (n⇧2)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n⇧2 = 2*(2*k*(k+1))+1"
    proof -
      have "n⇧2 = (2*k+1)⇧2"
        by (simp add: ‹n = 2 * k + 1›)
      also have "… = 4*k⇧2+4*k+1"
        by algebra
      also have "… = 2*(2*k*(k+1))+1"
        by algebra
      finally show "n⇧2 = 2*(2*k*(k+1))+1" .
    qed
    then have "∃k'. n⇧2 = 2*k'+1"
      by (rule exI)
    then have "odd (n⇧2)"
      by fastforce
    then show False
      using ‹even (n⇧2)› by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n⇧2 = 2*(2*k⇧2)"
    by simp
  then show "even (n⇧2)"
    by simp
qed

(* 2ª demostración *)

lemma
  fixes n :: int
  shows "even (n⇧2) ⟷ even n"
proof
  assume "even (n⇧2)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n⇧2 = 2*(2*k*(k+1))+1"
      by algebra
    then have "odd (n⇧2)"
      by simp
    then show False
      using ‹even (n⇧2)› by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n⇧2 = 2*(2*k⇧2)"
    by simp
  then show "even (n⇧2)"
    by simp
qed

(* 3ª demostración *)

lemma
  fixes n :: int
  shows "even (n⇧2) ⟷ even n"
proof -
  have "even (n⇧2) = (even n ∧ (0::nat) < 2)"
    by (simp only: even_power)
  also have "… = (even n ∧ True)"
    by (simp only: less_numeral_simps)
  also have "… = even n"
    by (simp only: HOL.simp_thms(21))
  finally show "even (n⇧2) ⟷ even n"
    by this
qed

(* 4ª demostración *)

lemma
  fixes n :: int
  shows "even (n⇧2) ⟷ even n"
proof -
  have "even (n⇧2) = (even n ∧ (0::nat) < 2)"
    by (simp only: even_power)
  also have "… = even n"
    by simp
  finally show "even (n⇧2) ⟷ even n" .
qed

(* 5ª demostración *)

lemma
  fixes n :: int
  shows "even (n⇧2) ⟷ even n"
  by simp

end
</pre>
