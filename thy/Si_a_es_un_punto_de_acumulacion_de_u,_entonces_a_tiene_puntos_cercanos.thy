(* Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.thy
-- Si a es un punto de acumulación de u, entonces (\<forall>\<epsilon>>0)(\<forall>n\<in>\<nat>)(\<exists>k\<ge>n)[u(k)−a| < \<epsilon>]
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-julio-2024
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
-- También se puede definir que a es un límite de u por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"
--
-- Los puntos de acumulación de una sucesión son los límites de sus
-- subsucesiones. En Lean se puede definir por
--    definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"
--
-- Demostrar que si a es un punto de acumulación de u, entonces
--    \<forall>\<epsilon>>0. \<forall> N. \<exists>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>
-- ------------------------------------------------------------------ *)

theory "Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos"
imports Main HOL.Real
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"

definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"

(* En la demostración se usarán los siguientes lemas *)

lemma aux1 :
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

lemma aux2 :
  assumes "extraccion \<phi>"
  shows   "\<forall> N N'. \<exists> k \<ge> N'. \<phi> k \<ge> N"
proof (intro allI)
  fix N N' :: nat
  have "max N N' \<ge> N' \<and> \<phi> (max N N') \<ge> N"
    by (meson assms aux1 max.bounded_iff max.cobounded2)
  then show "\<exists>k \<ge> N'. \<phi> k \<ge> N"
    by blast
qed

(* 1\<ordfeminine> demostración *)

lemma
  assumes "punto_acumulacion u a"
  shows   "\<forall>\<epsilon>>0. \<forall> N. \<exists>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
proof (intro allI impI)
  fix \<epsilon> :: real and N :: nat
  assume "\<epsilon> > 0"
  obtain \<phi> where h\<phi>1 : "extraccion \<phi>"
             and h\<phi>2 : "limite (u \<circ> \<phi>) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "\<forall>k\<ge>N'. \<bar>(u \<circ> \<phi>) k - a\<bar> < \<epsilon>"
    using h\<phi>2 limite_def \<open>\<epsilon> > 0\<close> by auto
  obtain m where hm1 : "m \<ge> N'" and hm2 : "\<phi> m \<ge> N"
    using aux2 h\<phi>1 by blast
  have "\<phi> m \<ge> N \<and> \<bar>u (\<phi> m) - a\<bar> < \<epsilon>"
    using hN' hm1 hm2 by force
  then show "\<exists>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
    by auto
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "punto_acumulacion u a"
  shows   "\<forall>\<epsilon>>0. \<forall> N. \<exists>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
proof (intro allI impI)
  fix \<epsilon> :: real and N :: nat
  assume "\<epsilon> > 0"
  obtain \<phi> where h\<phi>1 : "extraccion \<phi>"
             and h\<phi>2 : "limite (u \<circ> \<phi>) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "\<forall>k\<ge>N'. \<bar>(u \<circ> \<phi>) k - a\<bar> < \<epsilon>"
    using h\<phi>2 limite_def \<open>\<epsilon> > 0\<close> by auto
  obtain m where "m \<ge> N' \<and> \<phi> m \<ge> N"
    using aux2 h\<phi>1 by blast
  then show "\<exists>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
    using hN' by auto
qed

end
