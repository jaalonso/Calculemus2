---
title: Equivalence of definitions of the Fibonacci function
date: 2024-08-29 06:00:00 UTC+02:00
category: Induction
has_math: true
---

[mathjax]

In Lean4, the Fibonacci function can be defined as
<pre lang="haskell">
   def fibonacci : Nat → Nat
     | 0     => 0
     | 1     => 1
     | n + 2 => fibonacci n + fibonacci (n+1)
</pre>

Another more efficient definition is
<pre lang="haskell">
   def fib (n : Nat) : Nat :=
     (loop n).1
   where
     loop : Nat → Nat × Nat
       | 0   => (0, 1)
       | n + 1 =>
         let p := loop n
         (p.2, p.1 + p.2)
</pre>

Prove that both definitions are equivalent; that is,
<pre lang="haskell">
   fibonacci = fib
</pre>

To do this, complete the following Lean4 theory:

<pre lang="lean">
open Nat

set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

example : fibonacci = fib :=
by sorry
</pre>
<!--more-->

<h2>1. Proof in natural language</h2>

From the definition of the mirror function, we have the following lemma
<pre lang="haskell">
   fib_suma : fib (n + 2) = fib n + fib (n + 1)
</pre>

We need to prove that, for all n ∈ ℕ,
<pre lang="haskell">
   fibonacci n = fib n
</pre>
We will prove this by induction on n

**Case 1**: Suppose that n = 0. Then,

    fibonacci n = fibonacci 0
                = 1

and

    fib n = fib 0
          = (loop 0).1
          = (0, 1).1
          = 1

Therefore,

    fibonacci n = fib n

**Case 2**: Suppose that n = 1. Then,

    fibonacci n = 1

and

    fib 1 = (loop 1).1
          = (p.2, p.1 + p.2).1
            donde p = loop 0
          = ((0, 1).2, (0, 1).1 + (0, 1).2).1
          = (1, 0 + 1).1
          = 1

Therefore,

    fibonacci n = fib n

**Case 3**: Suppose that n = m + 2 and that the induction hypotheses hold,

    ih1 : fibonacci n = fib n
    ih2 : fibonacci (n + 1) = fib (n + 1)

Then,

    fibonacci n
    = fibonacci (m + 2)
    = fibonacci m + fibonacci (m + 1)
    = fib m + fib (m + 1)                [por ih1, ih2]
    = fib (m + 2)                        [por fib_suma]
    = fib n

<h2>2. Proofs with Lean4</h2>

<pre lang="lean">
open Nat

set_option pp.fieldNotation false

def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n+1)

def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

-- Auxiliary lemma
-- ===============

theorem fib_suma (n : Nat) : fib (n + 2) = fib n + fib (n + 1) :=
by rfl

-- Proof 1
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    rw [fib_suma]
    -- ⊢ fibonacci (succ (succ n)) = fib n + fib (n + 1)
    rw [fibonacci]
    -- ⊢ fibonacci n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [ih1]
    -- ⊢ fib n + fibonacci (n + 1) = fib n + fib (n + 1)
    rw [ih2]

-- Proof 2
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    calc fibonacci (succ (succ n))
         = fibonacci n + fibonacci (n + 1) := by rw [fibonacci]
       _ = fib n + fib (n + 1)             := by rw [ih1, ih2]
       _ = fib (succ (succ n))             := by rw [fib_suma]

-- Proof 3
-- =======

example : fibonacci = fib :=
by
  ext n
  -- n : Nat
  -- ⊢ fibonacci n = fib n
  induction n using fibonacci.induct with
  | case1 =>
    -- ⊢ fibonacci 0 = fib 0
    rfl
  | case2 =>
    -- ⊢ fibonacci 1 = fib 1
    rfl
  | case3 n ih1 ih2 =>
    -- n : Nat
    -- ih1 : fibonacci n = fib n
    -- ih2 : fibonacci (n + 1) = fib (n + 1)
    -- ⊢ fibonacci (succ (succ n)) = fib (succ (succ n))
    simp [ih1, ih2, fibonacci, fib_suma]
</pre>

You can interact with the previous proofs at [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Fibonacci.lean).

<h2>3. Proofs with Isabelle/HOL</h2>

<pre lang="isar">
theory Fibonacci
imports Main
begin

fun fibonacci :: "nat ⇒ nat"
  where
    "fibonacci 0 = 0"
  | "fibonacci (Suc 0) = 1"
  | "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"

fun fibAux :: "nat => nat × nat"
  where
     "fibAux 0 = (0, 1)"
   | "fibAux (Suc n) = (let (a, b) = fibAux n in (b, a + b))"

definition fib :: "nat ⇒ nat" where
  "fib n = fst (fibAux n)"

lemma fib_suma :
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"
proof (induct n)
  show "fib (Suc (Suc 0)) = fib 0 + fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume IH : "fib (Suc (Suc n)) = fib n + fib (Suc n)"
  have "fib (Suc (Suc (Suc n))) = fst (fibAux (Suc (Suc (Suc n))))"
    by (simp add: fib_def)
  also have "… = snd (fibAux (Suc (Suc n)))"
    by (simp add: prod.case_eq_if)
  also have "… = fst (fibAux (Suc n)) + snd (fibAux (Suc n))"
    by (metis fibAux.simps(2) snd_conv split_def)
  also have "… = fib (Suc n) + snd (fibAux (Suc n))"
    using fib_def by auto
  also have "… = fib (Suc n) + fib (Suc (Suc n))"
    by (simp add: fib_def prod.case_eq_if)
  finally show "fib (Suc (Suc (Suc n))) = fib (Suc n) + fib (Suc (Suc n))"
    by this
qed

lemma "fibonacci n = fib n"
proof (induct n rule: fibonacci.induct)
  show "fibonacci 0 = fib 0"
    by (simp add: fib_def)
next
  show "fibonacci (Suc 0) = fib (Suc 0)"
    by (simp add: fib_def)
next
  fix n
  assume IH1 : "fibonacci n = fib n"
  assume IH2 : "fibonacci (Suc n) = fib (Suc n)"
  have "fibonacci (Suc (Suc n)) = fibonacci n + fibonacci (Suc n)"
    by simp
  also have "… = fib n + fib (Suc n)"
    by (simp add: IH1 IH2)
  also have "… = fib (Suc (Suc n))"
    by (simp add: fib_suma)
  finally show "fibonacci (Suc (Suc n)) = fib (Suc (Suc n))"
    by this
qed

end
</pre>
