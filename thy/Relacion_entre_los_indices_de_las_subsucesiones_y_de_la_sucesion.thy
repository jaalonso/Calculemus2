(* Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.thy
-- Relación entre los índices de las subsucesiones y los de la sucesión.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción \<phi> tal que \<phi>(n) = 2*n.
--
-- En Isabelle/HOL, se puede definir que \<phi> es una función de
-- extracción por
--    definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
--      "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"
--
-- Demostrar que si \<phi> es una función de extracción, entonces
--    \<forall> n, n \<le> \<phi> n
-- ------------------------------------------------------------------ *)

theory Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion
imports Main
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

(* En la demostración se usará el siguiente lema *)

lemma extraccionE:
  assumes "extraccion \<phi>"
          "n < m"
  shows   "\<phi> n < \<phi> m"
proof -
  have "\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m"
    using assms(1) by (unfold extraccion_def)
  then have "n < m \<longrightarrow> \<phi> n < \<phi> m"
    by (elim allE)
  then show "\<phi> n < \<phi> m"
    using assms(2) by (rule mp)
qed

(* 1\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0"
    by (rule le0)
next
  fix n
  assume "n \<le> \<phi> n"
  also have "\<phi> n < \<phi> (Suc n)"
  proof -
    have "n < Suc n"
      by (rule lessI)
    with assms show "\<phi> n < \<phi> (Suc n)"
      by (rule extraccionE)
  qed
  finally show "Suc n \<le> \<phi> (Suc n)"
    by (rule Suc_leI)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0"
    by (rule le0)
next
  fix n
  assume "n \<le> \<phi> n"
  also have "\<dots> < \<phi> (Suc n)"
  using assms
  proof (rule extraccionE)
    show "n < Suc n"
      by (rule lessI)
  qed
  finally show "Suc n \<le> \<phi> (Suc n)"
    by (rule Suc_leI)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0"
    by (rule le0)
next
  fix n
  assume "n \<le> \<phi> n"
  also have "\<dots> < \<phi> (Suc n)"
    by (rule extraccionE [OF assms lessI])
  finally show "Suc n \<le> \<phi> (Suc n)"
    by (rule Suc_leI)
qed

(* 4\<ordfeminine> demostración *)

lemma
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0"
    by simp
next
  fix n
  assume HI : "n \<le> \<phi> n"
  also have "\<phi> n < \<phi> (Suc n)"
    using assms extraccion_def by blast
  finally show "Suc n \<le> \<phi> (Suc n)"
    by simp
qed

end
