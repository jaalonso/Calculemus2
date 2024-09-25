(* Brahmagupta-Fibonacci_identity.thy
-- Brahmagupta–Fibonacci identity.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, September 25, 2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove the Brahmagupta-Fibonacci Identity https://is.gd/9PJ56H
--    (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
-- ------------------------------------------------------------------ *)

theory "Brahmagupta-Fibonacci_identity"
imports Main HOL.Real
begin

(* Proof 1 *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_right)
  also have "\<dots> = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_left)
  also have "\<dots> = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)"
    by (simp only: distrib_left)
  also have "\<dots> = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)"
    by algebra
  also have "\<dots> = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) +
                  ((a*d)^2 + 2*a*d*b*c + (b*c)^2)"
    by algebra
  also have "\<dots> = (a*c - b*d)^2 + (a*d + b*c)^2"
    by algebra
  finally show "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2" .
qed

(* Proof 2 *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
by algebra

end
