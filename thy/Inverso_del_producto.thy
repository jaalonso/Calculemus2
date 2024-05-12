(* Inverso_del_producto.thy
-- Si G es un grupo y a, b \<in> G, entonces (ab)⁻¹ = b⁻¹a⁻¹
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea G un grupo y a, b \<in> G. Entonces,
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ------------------------------------------------------------------ *)

theory Inverso_del_producto
imports Main
begin

context group
begin

(* 1\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "(a \<^bold>* b) \<^bold>* (inverse b \<^bold>* inverse a) =
        ((a \<^bold>* b) \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* inverse b)) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* \<^bold>1) \<^bold>* inverse a"
    by (simp only: right_inverse)
  also have "\<dots> = a \<^bold>* inverse a"
    by (simp only: right_neutral)
  also have "\<dots> = \<^bold>1"
    by (simp only: right_inverse)
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "(a \<^bold>* b) \<^bold>* (inverse b \<^bold>* inverse a) =
        ((a \<^bold>* b) \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* inverse b)) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* \<^bold>1) \<^bold>* inverse a"
    by simp
  also have "\<dots> = a \<^bold>* inverse a"
    by simp
  also have "\<dots> = \<^bold>1"
    by simp
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1"
    .
qed

(* 3\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) =
        a \<^bold>* (b \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = \<^bold>1"
    by simp
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1" .
qed

(* 4\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
  by (simp only: inverse_distrib_swap)


end

end
