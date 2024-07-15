(* Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.thy
-- Las subsucesiones tienen el mismo límite que la sucesión.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-julio-2024
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
-- y que a es un límite de u por
--    definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
--      where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"
--
-- Demostrar que las subsucesiones de una sucesión convergente tienen el
-- mismo límite que la sucesión.
-- ------------------------------------------------------------------ *)

theory Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion
imports Main HOL.Real
begin

definition extraccion :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "extraccion \<phi> \<longleftrightarrow> (\<forall> n m. n < m \<longrightarrow> \<phi> n < \<phi> m)"

definition subsucesion :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool"
  where "subsucesion v u \<longleftrightarrow> (\<exists> \<phi>. extraccion \<phi> \<and> v = u \<circ> \<phi>)"

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. \<bar>u k - a\<bar> < \<epsilon>)"

(* En la demostración se usará el siguiente lema *)

lemma aux :
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

(* Demostración *)

lemma
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
      by (simp add: aux h\<phi>1)
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

end
