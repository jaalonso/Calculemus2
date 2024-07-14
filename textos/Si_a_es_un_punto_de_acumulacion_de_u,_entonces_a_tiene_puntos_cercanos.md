---
title: Si a es un punto de acumulación de u, entonces (∀ε>0)(∀n∈ℕ)(∃k≥n)[u(k)−a| < ε]
date: 2024-07-14 06:00:00 UTC+02:00
category: Límites
has_math: true
---

[mathjax]

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
\[ u_0, u_2, u_4, u_6, ... \]
se ha obtenido con la función de extracción \(φ\) tal que \(φ(n) = 2n\).

En Lean4, se puede definir que \(φ\) es una función de extracción por
<pre lang="lean">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
También se puede definir que \(a\) es un límite de \(u\) por
<pre lang="lean">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ n, ∀ k ≥ n, |u k - a| < ε
</pre>

Los puntos de acumulación de una sucesión son los límites de sus subsucesiones. En Lean4 se puede definir por
<pre lang="lean">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>

Demostrar que si \(a\) es un punto de acumulación de \(u\), entonces
\[ (∀ ε > 0)(∀ n ∈ ℕ)(∃ k ≥ n)[|u(k) - a| < ε \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic
open Nat

variable {u : ℕ → ℝ}
variable {a : ℝ}
variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ n, ∀ k ≥ n, |u k - a| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ n, ∃ k ≥ n, |u k - a| < ε :=
by sorry
</pre>
<!--more-->

<h2>1. Demostración en lenguaje natural</h2>

En la demostración usaremos el siguiente lema demostrado en el ejercicio anterior: Si \(φ\) es una función de extracción, entonces
\[ (∀ N, N')(∃ n ≥ N')[φ(n) ≥ N] \]

Por ser \(a\) un punto de acumulación de \(u\), existe una función de extracción \(φ\) tal que \(a\) es el límite de \(u ∘ φ\). Luego, para cada \(ε > 0\), existe un \(n' ∈ ℕ) tal que para todo \(k ≥ n'\),
\[ |(u ∘ φ)(k) - a| < ε \tag{1} \]
Por el lema 2, existe un \(m ∈ ℕ\) tal que
\begin{align}
   &m ≥ n'   \tag{2} \\
   &φ(m) ≥ n \tag{3}
\end{align}
Entonces, por (2) y (1),
\[ |(u ∘ φ)(m) - a| < ε \tag{4} \]                                           (4)
Luego, por (3) y (4), se tiene que
\[ φ(m) ≥ n ∧ |u(φ)(m)) - a| < ε \]
que es lo que había que demostrar.

<h2>2. Demostraciones con Lean4</h2>

<pre lang="lean">
</pre>

Se puede interactuar con las demostraciones anteriores en [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.lean).

<h2>3. Demostraciones con Isabelle/HOL</h2>

<pre lang="isar">
theory "Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos"
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

(* En la demostración se usarán los siguientes lemas *)

lemma aux1 :
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0" by simp
next
  fix n assume HI : "n ≤ φ n"
  then show "Suc n ≤ φ (Suc n)"
    using assms extraccion_def
    by (metis Suc_leI lessI order_le_less_subst1)
qed

lemma aux2 :
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  have "max N N' ≥ N' ∧ φ (max N N') ≥ N"
    by (meson assms aux1 max.bounded_iff max.cobounded2)
  then show "∃k ≥ N'. φ k ≥ N"
    by blast
qed

(* 1ª demostración *)

lemma
  assumes "punto_acumulacion u a"
  shows   "∀ε>0. ∀ N. ∃k≥N. ¦u k - a¦ < ε"
proof (intro allI impI)
  fix ε :: real and N :: nat
  assume "ε > 0"
  obtain φ where hφ1 : "extraccion φ"
             and hφ2 : "limite (u ∘ φ) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "∀k≥N'. ¦(u ∘ φ) k - a¦ < ε"
    using hφ2 limite_def ‹ε > 0› by auto
  obtain m where hm1 : "m ≥ N'" and hm2 : "φ m ≥ N"
    using aux2 hφ1 by blast
  have "φ m ≥ N ∧ ¦u (φ m) - a¦ < ε"
    using hN' hm1 hm2 by force
  then show "∃k≥N. ¦u k - a¦ < ε"
    by auto
qed

(* 2ª demostración *)

lemma
  assumes "punto_acumulacion u a"
  shows   "∀ε>0. ∀ N. ∃k≥N. ¦u k - a¦ < ε"
proof (intro allI impI)
  fix ε :: real and N :: nat
  assume "ε > 0"
  obtain φ where hφ1 : "extraccion φ"
             and hφ2 : "limite (u ∘ φ) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "∀k≥N'. ¦(u ∘ φ) k - a¦ < ε"
    using hφ2 limite_def ‹ε > 0› by auto
  obtain m where "m ≥ N' ∧ φ m ≥ N"
    using aux2 hφ1 by blast
  then show "∃k≥N. ¦u k - a¦ < ε"
    using hN' by auto
qed

end
</pre>
