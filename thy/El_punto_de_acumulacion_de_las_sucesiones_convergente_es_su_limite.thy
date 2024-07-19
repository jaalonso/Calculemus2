(* El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.thy
-- El punto de acumulación de las sucesiones convergente es su límite.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción \<phi> tal que \<phi>(n) = 2*n.
--
-- En Isabelle/HOL, se puede definir que \<phi> es una función de extracción
-- por
--    definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
--      "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"
-- que v es una subsucesión de u por
--    definition subsucesion :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool"
--      where "subsucesion v u \<longleftrightarrow> (\<exists> \<phi>. extraccion \<phi> \<and> v = u \<circ> \<phi>)"
-- que a es un límite de u por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
--      "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"
-- que u es convergente por
--    definition convergente :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
--      "convergente u \<longleftrightarrow> (\<exists> a. limite u a)"
-- que a es un punto de acumulación de u por
--    definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"
--
-- Demostrar que si u es una sucesión convergente y a es un punto de
-- acumulación de u, entonces a es un límite de u.
-- ------------------------------------------------------------------ *)

theory El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite
imports Main HOL.Real
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

definition subsucesion :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool"
  where "subsucesion v u \<longleftrightarrow> (\<exists> \<phi>. extraccion \<phi> \<and> v = u \<circ> \<phi>)"

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

definition convergente :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
  "convergente u \<longleftrightarrow> (\<exists> a. limite u a)"

definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"

(* Lemas auxiliares *)

lemma unicidad_limite_aux :
  assumes "limite u a"
          "limite u b"
  shows   "b \<le> a"
proof (rule ccontr)
  assume "\<not> b \<le> a"
  let ?\<epsilon> = "b - a"
  have "0 < ?\<epsilon>/2"
    using \<open>\<not> b \<le> a\<close> by auto
  obtain A where hA : "\<forall>n\<ge>A. \<bar>u n - a\<bar> < ?\<epsilon>/2"
    using assms(1) limite_def \<open>0 < ?\<epsilon>/2\<close> by blast
  obtain B where hB : "\<forall>n\<ge>B. \<bar>u n - b\<bar> < ?\<epsilon>/2"
    using assms(2) limite_def \<open>0 < ?\<epsilon>/2\<close> by blast
  let ?C = "max A B"
  have hCa : "\<forall>n\<ge>?C. \<bar>u n - a\<bar> < ?\<epsilon>/2"
    using hA by simp
  have hCb : "\<forall>n\<ge>?C. \<bar>u n - b\<bar> < ?\<epsilon>/2"
    using hB by simp
  have "\<forall>n\<ge>?C. \<bar>a - b\<bar> < ?\<epsilon>"
  proof (intro allI impI)
    fix n assume "n \<ge> ?C"
    have "\<bar>a - b\<bar> = \<bar>(a - u n) + (u n - b)\<bar>" by simp
    also have "\<dots> \<le> \<bar>u n - a\<bar> + \<bar>u n - b\<bar>" by simp
    finally show "\<bar>a - b\<bar> < b - a"
      using hCa hCb \<open>n \<ge> ?C\<close> by fastforce
  qed
  then show False by fastforce
qed

lemma unicidad_limite :
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a \<le> b" using assms(2) assms(1)
    by (rule unicidad_limite_aux)
next
  show "b \<le> a" using assms(1) assms(2)
    by (rule unicidad_limite_aux)
qed

lemma limite_subsucesion_aux :
  assumes "extraccion \<phi>"
  shows   "n \<le> \<phi> n"
proof (induct n)
  show "0 \<le> \<phi> 0" by simp
next
  fix n assume HI : "n \<le> \<phi> n"
  then show "Suc n \<le> \<phi> (Suc n)"
    using assms extraccion_def
    by (metis Suc_leI lessI order_le_less_subst1)
qed

lemma limite_subsucesion :
  assumes "subsucesion v u"
          "limite u a"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  then obtain N where hN : "\<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
    using assms(2) limite_def by auto
  obtain \<phi> where h\<phi>1 : "extraccion \<phi>" and h\<phi>2 : "v = u \<circ> \<phi>"
    using assms(1) subsucesion_def by auto
  have "\<forall>k\<ge>N. \<bar>v k - a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix k
    assume "N \<le> k"
    also have "... \<le> \<phi> k"
      by (simp add: limite_subsucesion_aux h\<phi>1)
    finally have "N \<le> \<phi> k" .
    have "\<bar>v k - a\<bar> = \<bar>u (\<phi> k) - a\<bar>"
      using h\<phi>2 by simp
    also have "\<dots> < \<epsilon>"
      using hN \<open>N \<le> \<phi> k\<close> by simp
    finally show "\<bar>v k - a\<bar> < \<epsilon>" .
  qed
  then show "\<exists>N. \<forall>k\<ge>N. \<bar>v k - a\<bar> < \<epsilon>"
    by auto
qed

(* Demostración *)

lemma
  assumes "convergente u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof -
  obtain b where hb : "limite u b"
    using assms(1) convergente_def by auto
  obtain \<phi> where h\<phi>1 : "extraccion \<phi>" and
                 h\<phi>2 : "limite (u \<circ> \<phi>) a"
    using assms(2) punto_acumulacion_def  by auto
  have "limite (u \<circ> \<phi>) b"
    using h\<phi>1 hb limite_subsucesion subsucesion_def by blast
  with h\<phi>2 have "a = b"
    by (rule unicidad_limite)
  then show "limite u a"
    using hb by simp
qed

end
