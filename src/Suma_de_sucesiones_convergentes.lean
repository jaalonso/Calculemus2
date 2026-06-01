-- Suma_de_sucesiones_convergentes.lean
-- Si aₙ converge a L y bₙ a M, entonces aₙ+bₙ converge a L+M.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 1-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si la sucesión a converge a L y la b a M, entonces a+b
-- converge a L+M.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que probar que para todo ε ∈ ℝ, si
--    ε > 0                                                          (1)
-- entonces
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |(a + b)(n) - (L + M)| < ε]           (2)
--
-- Por (1), se tiene que
--    ε/2 > 0                                                        (3)
-- Por (3) y porque el límite de a es L, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |a(n) - L| < ε/2]
-- Sea N₁ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₁ → |a(n) - L| < ε/2]                            (4)
-- Por (3) y porque el límite de b es M, se tiene que
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |b(n) - M| < ε/2]
-- Sea N₂ ∈ ℕ tal que
--    (∀n ∈ ℕ)[n ≥ N₂ → |b(n) - M| < ε/2]                            (5)
-- Sea N = máx(N₁, N₂). Veamos que verifica la condición (1). Para ello,
-- sea n ∈ ℕ tal que n ≥ N. Entonces, n ≥ N₁ y n ≥ N₂. Por tanto, por
-- las propiedades (4) y (5) se tiene que
--    |a(n) - L| < ε/2                                               (6)
--    |b(n) - M| < ε/2                                               (7)
-- Finalmente,
--    |(a + b)(n) - (L + M)| = |(a(n) + b(n)) - (L + M)|
--                           = |(a(n) - L) + (b(n) - M)|
--                           ≤ |a(n) - L| + |b(n) - M|
--                           < ε / 2 + ε / 2                [por (6) y (7)
--                           = ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a b c : ℕ → ℝ}
variable {L M : ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

namespace Solucion1

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε / 2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ (n : ℕ), n ≥ Na → |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε / 2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ (n : ℕ), n ≥ Nb → |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ (n : ℕ), n ≥ max Na Nb → |(s + t) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(a + b) n - (L + M)| < ε
  calc |(a + b) n - (L + M)|
     = |(a n + b n) - (L + M)|  := rfl
   _ = |(a n - L) + (b n - M)|  := by ring_nf
   _ ≤ |a n - L| + |b n - M|    := abs_add_le _ _
   _ < ε / 2 + ε / 2            := add_lt_add (hNa n (le_of_max_le_left hn))
                                              (hNb n (le_of_max_le_right hn))
   _ = ε                        := add_halves ε

end Solucion1

-- 2ª demostración
-- ===============

namespace Solucion2

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε / 2) (half_pos hε)
  -- Na : ℕ
  -- hNa : ∀ (n : ℕ), n ≥ Na → |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε / 2) (half_pos hε)
  -- Nb : ℕ
  -- hNb : ∀ (n : ℕ), n ≥ Nb → |b n - M| < ε / 2
  refine ⟨max Na Nb, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  have nNa : n ≥ Na := le_of_max_le_left hn
  specialize hNa n nNa
  -- hNa : |a n - L| < ε / 2
  have nNb : n ≥ Nb := le_of_max_le_right hn
  specialize hNb n nNb
  -- hNb : |b n - M| < ε / 2
  calc |(a + b) n - (L + M)|
     = |(a n + b n) - (L + M)|  := rfl
   _ = |(a n - L) + (b n - M)|  := by ring_nf
   _ ≤ |a n - L| + |b n - M|    := by apply abs_add_le
   _ < ε / 2 + ε / 2            := by linarith [hNa, hNb]
   _ = ε                        := by apply add_halves

end Solucion2

-- 3ª demostración
-- ===============

namespace Solucion3

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ n ≥ max Na Nb, |(a + b) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  have hn₁ : n ≥ Na := le_of_max_le_left hn
  specialize hNa n hn₁
  -- hNa : |a n - L| < ε / 2
  have hn₂ : n ≥ Nb := le_of_max_le_right hn
  specialize hNb n hn₂
  -- hNb : |b n - M| < ε / 2
  calc |(a + b) n - (L + M)|
       = |(a n + b n) - (L + M)|  := by rfl
     _ = |(a n - L) + (b n -  M)| := by {congr; ring}
     _ ≤ |a n - L| + |b n -  M|   := by apply abs_add_le
     _ < ε / 2 + ε / 2            := by linarith
     _ = ε                        := by apply add_halves

end Solucion3

-- 4ª demostración
-- ===============

namespace Solucion4

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ n ≥ max Na Nb, |(a + b) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  obtain ⟨hn₁, hn₂⟩ := max_le_iff.mp hn
  -- hn₁ : n ≥ Na
  -- hn₂ : n ≥ Nb
  calc |(a + b) n - (L + M)|
       = |a n + b n - (L + M)|   := by rfl
     _ = |(a n - L) + (b n - M)| := by { congr; ring }
     _ ≤ |a n - L| + |b n - M|   := by apply abs_add_le
     _ < ε/2 + ε/2               := add_lt_add (hNa n hn₁) (hNb n hn₂)
     _ = ε                       := by simp

end Solucion4

-- 5ª demostración
-- ===============

namespace Solucion5

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ n ≥ max Na Nb, |(a + b) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  obtain ⟨hn₁, hn₂⟩ := max_le_iff.mp hn
  -- hn₁ : Na ≤ n
  -- hn₂ : Nb ≤ n
  have cota₁ : |a n - L| < ε/2 := hNa n hn₁
  have cota₂ : |b n - M| < ε/2 := hNb n hn₂
  calc |(a + b) n - (L + M)|
       = |(a n + b n) - (L + M)| := by rfl
     _ = |(a n - L) + (b n - M)| := by { congr; ring }
     _ ≤ |a n - L| + |b n - M|   := by apply abs_add_le
     _ < ε                       := by linarith

end Solucion5

-- 6ª demostración
-- ===============

namespace Solucion6

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε Hε
  -- ε : ℝ
  -- Hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ n ≥ max Na Nb, |(a + b) n - (L + M)| < ε
  have h1 : max Na Nb ≥ Na := le_max_left _ _
  have h2 : max Na Nb ≥ Nb := le_max_right _ _
  intros n Hn
  -- n : ℕ
  -- Hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  have h3 : |a n - L| < ε/2 := hNa n (by linarith)
  have h4 : |b n - M| < ε/2 := hNb n (by linarith)
  calc |(a + b) n - (L + M)|
       = |(a n + b n) - (L + M)|   := by rfl
     _ = |(a n - L) + (b n - M)|   := by {congr; ring }
     _ ≤ |(a n - L)| + |(b n - M)| := by apply abs_add_le
     _ < ε/2 + ε/2                 := by linarith
     _ = ε                         := by ring

end Solucion6

-- 7ª demostración
-- ===============

namespace Solucion7

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  (hc : ∀ n, c n = a n + b n)
  : LimSuc c (L + M) :=
by
  change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |c n - (L + M)| < ε
  -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |c n - (L + M)| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |c n - (L + M)| < ε
  change ∀ ε₁ > 0, ∃ Na : ℕ, ∀ n ≥ Na, |a n - L| < ε₁ at ha
  -- ha : ∀ ε₁ > 0, ∃ Na, ∀ n ≥ Na, |a n - L| < ε₁
  change ∀ ε₂ > 0, ∃ Nb : ℕ, ∀ n ≥ Nb, |b n - M| < ε₂ at hb
  -- hb : ∀ ε₂ > 0, ∃ Nb, ∀ n ≥ Nb, |b n - M| < ε₂
  specialize ha (ε / 2)
  -- ha : ε / 2 > 0 → ∃ Na, ∀ n ≥ Na, |a n - L| < ε / 2
  specialize hb (ε / 2)
  -- ⊢ ∃ N, ∀ n ≥ N, |c n - (L + M)| < ε
  have hε2 : 0 < ε / 2 := by linarith [hε]
  specialize ha hε2
  -- ha : ∃ Na, ∀ n ≥ Na, |a n - L| < ε / 2
  specialize hb hε2
  -- hb : ∃ Nb, ∀ n ≥ Nb, |b n - M| < ε / 2
  choose Na hNa using ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  choose Nb hNb using hb
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use Na + Nb
  -- ⊢ ∀ n ≥ Na + Nb, |c n - (L + M)| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ Na + Nb
  -- ⊢ |c n - (L + M)| < ε
  specialize hc n
  -- hc : c n = a n + b n
  rewrite [hc]
  -- ⊢ |a n + b n - (L + M)| < ε
  have h1 : a n + b n - (L + M) =
    (a n - L) + (b n - M) := by ring_nf
  rewrite [h1]
  -- ⊢ |a n - L + (b n - M)| < ε
  specialize hNa n
  -- hNa : n ≥ Na → |a n - L| < ε / 2
  specialize hNb n
  -- hNb : n ≥ Nb → |b n - M| < ε / 2
  have h2 : Na ≤ n := by linarith
  have h3 : Nb ≤ n := by linarith
  specialize hNa h2
  -- hNa : |a n - L| < ε / 2
  specialize hNb h3
  -- hNb : |b n - M| < ε / 2
  have h4 : |a n - L + (b n - M)| ≤
    |a n - L| + |(b n - M)| := by apply abs_add_le
  linarith [abs_add_le (a n - L) (b n - M)]

end Solucion7

-- 8ª demostración
-- ===============

namespace Solucion8

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε/2) (by linarith)
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε/2) (by linarith)
  -- Nb : ℕ
  -- hNb : ∀ n ≥ Nb, |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ n ≥ max Na Nb, |(a + b) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nb
  -- ⊢ |(a + b) n - (L + M)| < ε
  specialize hNa n (le_of_max_le_left hn)
  -- hNa : |a n - L| < ε / 2
  specialize hNb n (le_of_max_le_right hn)
  -- hNb : |b n - M| < ε / 2
  simp
  -- ⊢ |a n + b n - (L + M)| < ε
  grind

end Solucion8

-- 9ª demostración
-- ===============

namespace Solucion9

example
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a + b) (L + M) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(a + b) n - (L + M)| < ε
  obtain ⟨Na, hNa⟩ := ha (ε / 2) (by grind)
  -- Na : ℕ
  -- hNa : ∀ (n : ℕ), n ≥ Na → |a n - L| < ε / 2
  obtain ⟨Nb, hNb⟩ := hb (ε / 2) (by grind)
  -- Nb : ℕ
  -- hNb : ∀ (n : ℕ), n ≥ Nb → |b n - M| < ε / 2
  use max Na Nb
  -- ⊢ ∀ (n : ℕ), n ≥ max Na Nb → |(s + t) n - (L + M)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |(a + b) n - (L + M)| < ε
  calc |(a + b) n - (L + M)|
     = |(a n + b n) - (L + M)|  := rfl
   _ = |(a n - L) + (b n - M)|  := by grind
   _ ≤ |a n - L| + |b n - M|    := by grind
   _ < ε / 2 + ε / 2            := by grind
   _ = ε                        := by grind

end Solucion9

-- Lemas usados
-- ============

variable (x y z z' : ℝ)
#check (abs_add_le x y : |x + y| ≤ |x| + |y|)
#check (add_halves x : x / 2 + x / 2 = x)
#check (add_lt_add : x < y → z < z' → x + z < y + z')
#check (half_pos : x > 0 → x / 2 > 0)
#check (le_max_left x y : x ≤ max x y)
#check (le_max_right x y : y ≤ max x y)
#check (le_of_max_le_left : max x y ≤ z → x ≤ z)
#check (le_of_max_le_right : max x y ≤ z → y ≤ z)
#check (max_le_iff : max x y ≤ z ↔ x ≤ z ∧ y ≤ z)
