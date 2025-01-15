---
title: Praeclarum theorema
date: 2020-02-24 06:00:00 UTC+02:00
category: Proposicional
has_math: true
---

Demostrar con Isabelle/HOL el [Praeclarum theorema](https://tinyurl.com/25yt3ef9) de Leibniz:
\\[ (p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s)) \\]

Para ello, completar la siguiente teoría
~~~isabelle
theory Praeclarum_theorema
imports Main
begin

lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  oops

end
~~~

## Soluciones con Isabelle/HOL

~~~isabelle
theory Praeclarum_theorema
imports Main
begin

(* 1ª demostración: detallada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof (rule impI)
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof (rule impI)
    assume "p ∧ r"
    show "q ∧ s"
    proof (rule conjI)
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct1)
      moreover have "p" using ‹p ∧ r› by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct2)
      moreover have "r" using ‹p ∧ r› by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

(* 2ª demostración: estructurada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof
    assume "p ∧ r"
    show "q ∧ s"
    proof
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "p" using ‹p ∧ r› ..
      ultimately show "q" ..
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "r" using ‹p ∧ r› ..
      ultimately show "s" ..
    qed
  qed
qed

(* 3ª demostración: aplicativa *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* 4ª demostración: automática *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  by simp

end
~~~
