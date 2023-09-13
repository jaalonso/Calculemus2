---
Título: En ℝ, {0 < ε, ε ≤ 1, |x| < ε, |y| < ε} ⊢ |xy| < ε
Autor:  José A. Alonso
---

Demostrar con Lean4 que en ℝ
\[ \{0 < ε, ε ≤ 1, |x| < ε, |y| < ε\} ⊢ |xy| < ε \]

Para ello, completar la siguiente teoría de Lean4:

<pre lang="lean">
import Mathlib.Data.Real.Basic

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by sorry
</pre>
<!--more-->

<b>Demostración en lenguaje natural</b>

[mathjax]
Se usarán los siguientes lemas
\begin{align}
   &|a·b| = |a|·|b|            \tag{L1} \\
   &0·a = 0                    \tag{L2} \\
   &0 ≤ |a|                    \tag{L3} \\
   &a ≤ b → a ≠ b → a < b      \tag{L4} \\
   &a ≠ b ↔ b ≠ a              \tag{L5} \\
   &0 < a → (ab < ac ↔ b < c)  \tag{L6} \\
   &0 < a → (ba < ca ↔ b < c)  \tag{L7} \\
   &0 < a → (ba ≤ ca ↔ b ≤ c)  \tag{L8} \\
   &1·a = a                    \tag{L9} \\
\end{align}

Sean \(x, y, ε ∈ ℝ\) tales que
\begin{align}
   0   &< ε \tag{he1} \\
   ε   &≤ 1 \tag{he2} \\
   |x| &< ε \tag{hx} \\
   |y| &< ε \tag{hy}
\end{align}
y tenemos que demostrar que
\[   |xy| < ε \]
Lo haremos distinguiendo caso según \(|x| = 0\).

1º caso. Supongamos que
\[   |x| = 0 \tag{1} \]
Entonces,
\begin{align}
   |xy| &= |x||y|    &&\text{[por L1]} \\
        &= 0|y|      &&\text{[por h1]} \\
        &= 0         &&\text{[por L2]} \\
        &< ε         &&\text{[por he1]}
\end{align}

2º caso. Supongamos que
\[ |x| ≠ 0 \tag{2} \]
Entonces, por L4, L3 y L5, se tiene
\[ 0 < x \tag{3} \]
y, por tanto,
\begin{align}
   |xy| &= |x||y|    &&\text{[por L1]} \\
        &< |x|ε      &&\text{[por L6, (3) y (hy)]} \\
        &< εε        &&\text{[por L7, (he1) y (hx)]} \\
        &≤ 1ε        &&\text{[por L8, (he1) y (he2)]} \\
        &= ε         &&\text{[por L9]}
\end{align}

<b>Demostraciones con Lean4</b>

<pre lang="lean">
import Mathlib.Data.Real.Basic

-- 1ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases h : (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc
      |x * y|
         = |x| * |y| := abs_mul x y
      _  = 0 * |y|   := by rw [h]
      _  = 0         := zero_mul (abs y)
      _  < ε         := he1
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := abs_nonneg x
      show 0 < |x|
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc |x * y|
         = |x| * |y| := abs_mul x y
       _ < |x| * ε   := (mul_lt_mul_left h1).mpr hy
       _ < ε * ε     := (mul_lt_mul_right he1).mpr hx
       _ ≤ 1 * ε     := (mul_le_mul_right he1).mpr he2
       _ = ε         := one_mul ε

-- 2ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by apply abs_mul
            _ = 0 * |y|   := by rw [h]
            _ = 0         := by apply zero_mul
            _ < ε         := by apply he1
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := by apply abs_nonneg
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by rw [abs_mul]
            _ < |x| * ε   := by apply (mul_lt_mul_left h1).mpr hy
            _ < ε * ε     := by apply (mul_lt_mul_right he1).mpr hx
            _ ≤ 1 * ε     := by apply (mul_le_mul_right he1).mpr he2
            _ = ε         := by rw [one_mul]

-- 3ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intros x y ε he1 he2 hx hy
  by_cases (|x| = 0)
  . -- h : |x| = 0
    show |x * y| < ε
    calc |x * y| = |x| * |y| := by simp only [abs_mul]
               _ = 0 * |y|   := by simp only [h]
               _ = 0         := by simp only [zero_mul]
               _ < ε         := by simp only [he1]
  . -- h : ¬|x| = 0
    have h1 : 0 < |x| := by
      have h2 : 0 ≤ |x| := by simp only [abs_nonneg]
      exact lt_of_le_of_ne h2 (ne_comm.mpr h)
    show |x * y| < ε
    calc
      |x * y| = |x| * |y| := by simp [abs_mul]
            _ < |x| * ε   := by simp only [mul_lt_mul_left, h1, hy]
            _ < ε * ε     := by simp only [mul_lt_mul_right, he1, hx]
            _ ≤ 1 * ε     := by simp only [mul_le_mul_right, he1, he2]
            _ = ε         := by simp only [one_mul]

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (abs_mul a b : |a * b| = |a| * |b|)
-- #check (abs_nonneg a : 0 ≤ |a|)
-- #check (lt_of_le_of_ne : a ≤ b → a ≠ b → a < b)
-- #check (mul_le_mul_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c))
-- #check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
-- #check (mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c))
-- #check (ne_comm : a ≠ b ↔ b ≠ a)
-- #check (one_mul a : 1 * a = a)
-- #check (zero_mul a : 0 * a = 0)
</pre>

<b>Demostraciones interactivas</b>

Se puede interactuar con las demostraciones anteriores en <a href="https://lean.math.hhu.de/#url=https://raw.githubusercontent.com/jaalonso/Calculemus2/main/src/Acotacion_del_producto.lean" rel="noopener noreferrer" target="_blank">Lean 4 Web</a>.

<b>Referencias</b>

<ul>
<li> J. Avigad y P. Massot. <a href="https://bit.ly/3U4UjBk">Mathematics in Lean</a>, p. 24.</li>
</ul>
