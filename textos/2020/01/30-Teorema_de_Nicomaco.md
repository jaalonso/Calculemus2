---
title: Teorema de Nicómaco
date: 2020-01-30 06:00:00 UTC+02:00
category: Inducción
has_math: true
---

Demostrar el [teorema de Nicómaco](http://bit.ly/2OaJI7q) que afirma que la suma de los cubos de los \\(n\\) primeros números naturales es igual que el cuadrado de la suma de los \\(n\\) primeros números naturales; es decir, para todo número natural n se tiene que
\\[ 1^3 + 2^3 + ... + n^3 = (1 + 2 + ... + n)^2 \\]

Para ello, completar la siguiente teoría de Lean4:

~~~lean
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable ( n : ℕ)

def suma : ℕ → ℕ
  | 0      => 0
  | succ n => suma n + (n+1)

def sumaCubos : ℕ → ℕ
  | 0   => 0
  | n+1 => sumaCubos n + (n+1)^3

example :
  sumaCubos n = (suma n)^2 :=
by sorry
~~~
<!-- TEASER_END -->

# 1. Demostración en lenguaje natural

Es consecuencia de las fórmulas de la suma de los primeros \\(n\\) números naturales y la de los cubos de los primeros \\(n\\) números naturales; es decir,

+ Lema 1: \\[1 + 2 + ... + n = \\dfrac{n(n+1)}{2} \\]
+ Lema 2: \\[1^3 + 2^3 + ... + n^3 = \\dfrac{(n(n+1))^2}{4} \\]

En efecto,

\\begin{align}
1^3 + 2^3 + ... + n^3
&= \\dfrac{(n(n+1))^2}{4}               &&\\text{[por el Lema 2]} \\newline
&= \\dfrac{2(1 + 2 + ... + n)^2}{4}    &&\\text{[por el Lema 1]} \\newline
&= (1 + 2 + ... + n)^2
\\end{align}

El Lema 1 es equivalente a
\\[ 2(1 + 2 + ... + n) = n(n+1) \\]
que se demuestra por inducción:

Caso base: Para \\(n = 0\\), la suma es \\(0\\) y
\\[ 2·0 = 0(0+1) \\]

Paso de inducción: Supongamos la hipótesis de inducción:
\\[ 2(1 + 2 + ... + n) = n(n+1) \\tag{HI} \\]
Entonces,
\\begin{align}
2(1 + 2 + ... + n + (n+1))
&= 2(1 + 2 + ... + n) + 2(n+1) \\newline
&= n(n+1) + 2(n+1)             &&\\text{[por la HI]} \\newline
&= (n+2)(n+1)                  \\newline
&= (n+1)((n+1)+1)
\\end{align}

El Lema 2 es equivalente a
\\[ 4(1^3 + 2^3 + ... + n^3) = (n(n+1))^2 \\]
que se demuestra por inducción:

Caso base: Para \\(n = 0\\), la suma es \\(0\\) y
\\[ 4·0 = (0(0+1))^2 \\]
Paso de inducción: Supongamos la hipótesis de inducción:
\\[ 4(1^3 + 2^3 + ... + n^3) = (n(n+1))^2 \\tag{HI} \\]
Entonces,
\\begin{align}
4(1^3 + 2^3 + ... + n^3 + (n+1)^3)
&= 4(1^3 + 2^3 + ... + n^3) + 4(n+1)^3 \\newline
&= (n(n+1))^2 + 4(n+1)^3             \\newline
&= (n+1)^2(n^2 + 4n + 4)             \\newline
&= ((n+1)((n+1)+1))^2
\\end{align}

# 2. Demostraciones con Lean4

~~~lean
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

open Nat

variable (m n : ℕ)

set_option pp.fieldNotation false

-- (suma n) es la suma de los n primeros números naturales.
def suma : ℕ → ℕ
  | 0      => 0
  | succ n => suma n + (n+1)

@[simp]
lemma suma_zero : suma 0 = 0 := rfl

@[simp]
lemma suma_succ : suma (n + 1) = suma n + (n+1) := rfl

-- (sumaCubos n) es la suma de los cubos de los n primeros números
-- naturales.
@[simp]
def sumaCubos : ℕ → ℕ
  | 0   => 0
  | n+1 => sumaCubos n + (n+1)^3

-- Lema 1: Fórmula para la suma de los primeros n números naturales.

-- 1ª demostración del lema 1
-- ==========================

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := congrArg (2 * .) suma_zero
       _ = 0           := mul_zero 2
       _ = 0 * (0 + 1) := zero_mul (0 + 1)
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := congrArg (2 * .) (suma_succ n)
       _ = 2 * suma n + 2 * (n + 1)  := mul_add 2 (suma n) (n + 1)
       _ = n * (n + 1) + 2 * (n + 1) := congrArg (. + 2 * (n + 1)) HI
       _ = (n + 2) * (n + 1)         := (add_mul n 2 (n + 1)).symm
       _ = (n + 1) * (n + 2)         := mul_comm (n + 2) (n + 1)

-- 2ª demostración del lema 1
-- ==========================

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    calc 2 * suma 0
         = 2 * 0       := rfl
       _ = 0           := rfl
       _ = 0 * (0 + 1) := rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 2) * (n + 1)         := by ring
       _ = (n + 1) * (n + 2)         := by ring

-- 3ª demostración del lema 1
-- ==========================

example :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero =>
    -- ⊢ 2 * suma 0 = 0 * (0 + 1)
    rfl
  | succ n HI =>
    -- n : ℕ
    -- HI : 2 * suma n = n * (n + 1)
    -- ⊢ 2 * suma (n + 1) = (n + 1) * (n + 1 + 1)
    calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    := rfl
       _ = 2 * suma n + 2 * (n + 1)  := by ring
       _ = n * (n + 1) + 2 * (n + 1) := by simp [HI]
       _ = (n + 1) * (n + 2)         := by ring

-- 4ª demostración del lema 1
-- ==========================

lemma formula_suma :
  2 * suma n = n * (n + 1) :=
by
  induction n with
  | zero => rfl
  | succ n HI => unfold suma ; linarith [HI]

-- Lema 2: Fórmula para la suma de de los cubos de los primeros n
-- números naturales.

-- 1ª demostración del lema 2
-- ==========================

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    -- ⊢ 4 * sumaCubos 0 = (0 * (0 + 1)) ^ 2
    calc 4 * sumaCubos 0
         = 4 * 0             := by simp only [sumaCubos]
       _ = (0 * (0 + 1)) ^ 2 := by simp
  | succ m HI =>
     -- m : ℕ
     -- HI : 4 * sumaCubos m = (m * (m + 1)) ^ 2
     -- ⊢ 4 * sumaCubos (m + 1) = ((m + 1) * (m + 1 + 1)) ^ 2
    calc 4 * sumaCubos (m + 1)
         = 4 * (sumaCubos m + (m+1)^3)
           := by simp only [sumaCubos]
       _ = 4 * sumaCubos m + 4*(m+1)^3
           := by ring
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = (m+1)^2*(m^2+4*m+4)
           := by ring
       _ = (m+1)^2*(m+2)^2
           := by ring
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1))^2
           := by simp

-- 2ª demostración del lema 2
-- ==========================

lemma formula_sumaCubos :
  4 * sumaCubos n = (n*(n+1))^2 :=
by
  induction n with
  | zero =>
    simp
  | succ m HI =>
    calc 4 * sumaCubos (m+1)
         = 4 * sumaCubos m + 4*(m+1)^3
           := by {simp ; ring_nf}
       _ = (m*(m+1))^2 + 4*(m+1)^3
           := congrArg (. + 4*(m+1)^3) HI
       _ = ((m+1)*(m+2))^2
           := by ring
       _ = ((m+1) * (m+1+1)) ^ 2
           := by simp

-- Teorema de Nicómaco

example :
  sumaCubos n = (suma n)^2 :=
by
  have h1 : 4 * sumaCubos n = 4 * (suma n)^2 :=
    calc 4 * sumaCubos n
       = (n*(n+1))^2    := by simp only [formula_sumaCubos]
     _ = (2 * suma n)^2 := by simp only [formula_suma]
     _ = 4 * (suma n)^2 := by ring
  linarith

-- Lemas usados
-- ============

-- variable (a b c : ℕ)
-- #check (add_mul a b c : (a + b) * c = a * c + b * c)
-- #check (mul_add a b c : a * (b + c) = a * b + a * c)
-- #check (mul_comm a b : a * b = b * a)
-- #check (mul_zero a : a * 0 = 0)
-- #check (zero_mul a : 0 * a = 0)
~~~

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2_es/main/src/Teorema_de_Nicomaco.lean).

# 3. Demostraciones con Isabelle/HOL

~~~isabelle
theory Teorema_de_Nicomaco
imports Main
begin

(* (suma n) es la suma de los primeros números naturales. *)
fun suma :: "nat ⇒ nat" where
  "suma 0 = 0"
| "suma (Suc n) = suma n + Suc n"

(* (sumaCubos n) es la suma de los cubos primeros números naturales. *)
fun sumaCubos :: "nat ⇒ nat" where
  "sumaCubos 0 = 0"
| "sumaCubos (Suc n) = sumaCubos n + (Suc n)^3"

(* Fórmula para la suma *)
lemma "2 * suma n = n^2 + n"
proof (induct n)
  show "2 * suma 0 = 0^2 + 0" by simp
next
  fix n
  assume "2 * suma n = n^2 + n"
  then have "2 * suma (Suc n) = n^2 + n + 2 + 2 * n"
    by simp
  also have "… = (Suc n)^2 + Suc n"
    by (simp add: power2_eq_square)
  finally show "2 * suma (Suc n) = (Suc n)^2 + Suc n"
    by this
qed

(* Demostración automática de la propiedad anterior *)
lemma formula_suma:
  "2 * suma n = n^2 + n"
  by (induct n) (auto simp add: power2_eq_square)

lemma "4 * sumaCubos n = (n^2 + n)^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0^2 + 0)^2"
    by simp
next
  fix n
  assume "4 * sumaCubos n = (n^2 + n)^2"
  then have "4 * sumaCubos (Suc n) = (n^2 + n)^2 + 4 * (Suc n)^3"
    by simp
  then show "4 * sumaCubos (Suc n) = ((Suc n)^2 + Suc n)^2"
  by (simp add: algebra_simps
                power2_eq_square
                power3_eq_cube )
qed

(* Demostración automática de la propiedad anterior *)
lemma formula_sumaCubos:
  "4 * sumaCubos n = (n^2 + n)^2"
  by (induct n) (auto simp add: algebra_simps
                                power2_eq_square
                                power3_eq_cube)

(* Lema auxiliar *)
lemma aux: "4 * (m::nat) = (2 * n)^2 ⟹ m = n^2"
  by (simp add: power2_eq_square)

(* Teorema de Nicómaco *)
theorem teorema_de_Nicomaco:
  "sumaCubos n = (suma n)^2"
  by (simp only: formula_suma formula_sumaCubos aux)

end
~~~
