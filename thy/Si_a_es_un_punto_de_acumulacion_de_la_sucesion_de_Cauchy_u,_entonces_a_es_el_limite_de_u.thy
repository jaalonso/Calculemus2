(* Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.thy
-- Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, una sucesión u₀, u₁, u₂, ... se puede representar
-- mediante una función (u : \<nat> \<rightarrow> \<real>) de forma que u(n) es uₙ.
--
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción \<phi> tal que \<phi>(n) = 2*n.
--
-- En Isabelle/HOL, se puede definir que \<phi> es una función de extracción
-- por
--    definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
--      "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"
-- que a es un límite de u por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"
-- que a es un punto de acumulación de u por
--    definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"
-- que la sucesión u es de Cauchy por
--    definition suc_cauchy :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
--      where "suc_cauchy u \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>)"
--
-- Demostrar que si u es una sucesión de Cauchy y a es un punto de
-- acumulación de u, entonces a es el límite de u.
-- ------------------------------------------------------------------ *)

theory "Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u"
imports Main HOL.Real
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"

definition punto_acumulacion :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "punto_acumulacion u a \<longleftrightarrow> (\<exists>\<phi>. extraccion \<phi> \<and> limite (u \<circ> \<phi>) a)"

definition suc_cauchy :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "suc_cauchy u \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>u m - u n\<bar> < \<epsilon>)"

(* Lemas auxiliares *)

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

lemma cerca_acumulacion :
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

(* Demostración *)

lemma
  assumes "suc_cauchy u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof (unfold limite_def; intro allI impI)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  then have "\<epsilon>/2 > 0"
    by simp
  then obtain N where hN : "\<forall>m\<ge>N. \<forall>n\<ge>N. \<bar>u m - u n\<bar> < \<epsilon>/2"
    using assms(1) suc_cauchy_def
    by blast
  have "\<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix k
    assume hk : "k \<ge> N"
    obtain N' where hN'1 : "N' \<ge> N" and
                    hN'2 : "\<bar>u N' - a\<bar> < \<epsilon>/2"
      using assms(2) cerca_acumulacion \<open>\<epsilon>/2 > 0\<close> by blast
    have "\<bar>u k - a\<bar> = \<bar>(u k - u N') + (u N'  - a)\<bar>"
      by simp
    also have "\<dots> \<le> \<bar>u k - u N'\<bar> + \<bar>u N'  - a\<bar>"
      by simp
    also have "\<dots> < \<epsilon>/2 + \<bar>u N'  - a\<bar>"
      using hk hN hN'1 by auto
    also have "\<dots> < \<epsilon>/2 + \<epsilon>/2"
      using hN'2 by auto
    also have "\<dots> = \<epsilon>"
      by simp
    finally show "\<bar>u k - a\<bar> < \<epsilon>" .
  qed
  then show "\<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>"
    by auto
qed

end
