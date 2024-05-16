(* Los_monoides_booleanos_son_conmutativos.thy
-- Los monoides booleanos son conmutativos
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 20-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Un monoide M es booleano si
--    \<forall> x \<in> M, x * x = 1
-- y es conmutativo si
--    \<forall> x y \<in> M, x * y = y * x
--
-- Demostrar que los monoides booleanos son conmutativos.
-- ------------------------------------------------------------------ *)

theory Los_monoides_booleanos_son_conmutativos
imports Main
begin

context monoid
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* x = \<^bold>1"
  shows   "\<forall> x y. x \<^bold>* y = y \<^bold>* x"
proof (rule allI)+
  fix a b
  have "a \<^bold>* b = (a \<^bold>* b) \<^bold>* \<^bold>1"
    by (simp only: right_neutral)
  also have "\<dots> = (a \<^bold>* b) \<^bold>* (a \<^bold>* a)"
    by (simp only: assms)
  also have "\<dots> = ((a \<^bold>* b) \<^bold>* a) \<^bold>* a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* a)) \<^bold>* a"
    by (simp only: assoc)
  also have "\<dots> = (\<^bold>1 \<^bold>* (a \<^bold>* (b \<^bold>* a))) \<^bold>* a"
    by (simp only: left_neutral)
  also have "\<dots> = ((b \<^bold>* b) \<^bold>* (a \<^bold>* (b \<^bold>* a))) \<^bold>* a"
    by (simp only: assms)
  also have "\<dots> = (b \<^bold>* (b \<^bold>* (a \<^bold>* (b \<^bold>* a)))) \<^bold>* a"
    by (simp only: assoc)
  also have "\<dots> = (b \<^bold>* ((b \<^bold>* a) \<^bold>* (b \<^bold>* a))) \<^bold>* a"
    by (simp only: assoc)
  also have "\<dots> = (b \<^bold>* \<^bold>1) \<^bold>* a"
    by (simp only: assms)
  also have "\<dots> = b \<^bold>* a"
    by (simp only: right_neutral)
  finally show "a \<^bold>* b = b \<^bold>* a"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* x = \<^bold>1"
  shows   "\<forall> x y. x \<^bold>* y = y \<^bold>* x"
proof (rule allI)+
  fix a b
  have "a \<^bold>* b = (a \<^bold>* b) \<^bold>* \<^bold>1"                     by simp
  also have "\<dots> = (a \<^bold>* b) \<^bold>* (a \<^bold>* a)"             by (simp add: assms)
  also have "\<dots> = ((a \<^bold>* b) \<^bold>* a) \<^bold>* a"             by (simp add: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* a)) \<^bold>* a"             by (simp add: assoc)
  also have "\<dots> = (\<^bold>1 \<^bold>* (a \<^bold>* (b \<^bold>* a))) \<^bold>* a"       by simp
  also have "\<dots> = ((b \<^bold>* b) \<^bold>* (a \<^bold>* (b \<^bold>* a))) \<^bold>* a" by (simp add: assms)
  also have "\<dots> = (b \<^bold>* (b \<^bold>* (a \<^bold>* (b \<^bold>* a)))) \<^bold>* a" by (simp add: assoc)
  also have "\<dots> = (b \<^bold>* ((b \<^bold>* a) \<^bold>* (b \<^bold>* a))) \<^bold>* a" by (simp add: assoc)
  also have "\<dots> = (b \<^bold>* \<^bold>1) \<^bold>* a"                   by (simp add: assms)
  also have "\<dots> = b \<^bold>* a"                         by simp
  finally show "a \<^bold>* b = b \<^bold>* a"                   by this
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* x = \<^bold>1"
  shows   "\<forall> x y. x \<^bold>* y = y \<^bold>* x"
proof (rule allI)+
  fix a b
  have "a \<^bold>* b = (a \<^bold>* b) \<^bold>* (a \<^bold>* a)"               by (simp add: assms)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* a)) \<^bold>* a"             by (simp add: assoc)
  also have "\<dots> = ((b \<^bold>* b) \<^bold>* (a \<^bold>* (b \<^bold>* a))) \<^bold>* a" by (simp add: assms)
  also have "\<dots> = (b \<^bold>* ((b \<^bold>* a) \<^bold>* (b \<^bold>* a))) \<^bold>* a" by (simp add: assoc)
  also have "\<dots> = (b \<^bold>* \<^bold>1) \<^bold>* a"                   by (simp add: assms)
  finally show "a \<^bold>* b = b \<^bold>* a"                   by simp
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "\<forall> x. x \<^bold>* x = \<^bold>1"
  shows   "\<forall> x y. x \<^bold>* y = y \<^bold>* x"
  by (metis assms assoc right_neutral)

end

end
