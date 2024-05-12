(* Inverso_del_inverso_en_grupos.thy
-- Si G un grupo y a \<in> G, entonces (a⁻¹)⁻¹ = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea G un grupo y a \<in> G. Demostrar que
--    (a⁻¹)⁻¹ = a
-- ------------------------------------------------------------------ *)

theory Inverso_del_inverso_en_grupos
imports Main
begin

context group
begin

(* 1\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) \<^bold>* \<^bold>1"
    by (simp only: right_neutral)
  also have "\<dots> = inverse (inverse a) \<^bold>* (inverse a \<^bold>* a)"
    by (simp only: left_inverse)
  also have "\<dots> = (inverse (inverse a) \<^bold>* inverse a) \<^bold>* a"
    by (simp only: assoc)
  also have "\<dots> = \<^bold>1 \<^bold>* a"
    by (simp only: left_inverse)
  also have "\<dots> = a"
    by (simp only: left_neutral)
  finally show "inverse (inverse a) = a"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
proof -
  have "inverse (inverse a) =
        (inverse (inverse a)) \<^bold>* \<^bold>1"                       by simp
  also have "\<dots> = inverse (inverse a) \<^bold>* (inverse a \<^bold>* a)" by simp
  also have "\<dots> = (inverse (inverse a) \<^bold>* inverse a) \<^bold>* a" by simp
  also have "\<dots> = \<^bold>1 \<^bold>* a"                                 by simp
  finally show "inverse (inverse a) = a"                 by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a \<^bold>* a = \<^bold>1"
    by (simp only: left_inverse)
qed

(* 4\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
proof (rule inverse_unique)
  show "inverse a \<^bold>* a = \<^bold>1" by simp
qed

(* 5\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
  by (rule inverse_unique) simp

(* 6\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
  by (simp only: inverse_inverse)

(* 7\<ordfeminine> demostración *)

lemma "inverse (inverse a) = a"
  by simp

end

end
