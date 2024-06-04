(* Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.thy
-- Si uₙ está acotada y lim vₙ = 0, entonces lim (uₙ\<sqdot>vₙ) = 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-junio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si uₙ está acotada y lim vₙ = 0, entonces
-- lim (uₙ\<sqdot>vₙ) = 0.
-- ------------------------------------------------------------------ *)

theory Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "limite u c \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>k::nat. \<forall>n\<ge>k. \<bar>u n - c\<bar> < \<epsilon>)"

definition acotada :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "acotada u \<longleftrightarrow> (\<exists>B. \<forall>n. \<bar>u n\<bar> \<le> B)"

lemma
  assumes "acotada u"
          "limite v 0"
  shows   "limite (\<lambda>n. u n * v n) 0"
proof -
  obtain B where hB : "\<forall>n. \<bar>u n\<bar> \<le> B"
    using assms(1) acotada_def by auto
  then have hBnoneg : "0 \<le> B" by auto
  show "limite (\<lambda>n. u n * v n) 0"
  proof (cases "B = 0")
    assume "B = 0"
    show "limite (\<lambda>n. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      have "\<forall>n\<ge>0. \<bar>u n * v n - 0\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix n :: nat
        assume "n \<ge> 0"
        show "\<bar>u n * v n - 0\<bar> < \<epsilon>"
          using \<open>0 < \<epsilon>\<close> \<open>B = 0\<close> hB by auto
      qed
      then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n * v n - 0\<bar> < \<epsilon>"
        by (rule exI)
    qed
  next
    assume "B \<noteq> 0"
    then have hBpos : "0 < B"
      using hBnoneg by auto
    show "limite (\<lambda>n. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      then have "0 < \<epsilon>/B"
        by (simp add: hBpos)
      then obtain N where hN : "\<forall>n\<ge>N. \<bar>v n - 0\<bar> < \<epsilon>/B"
        using assms(2) limite_def by auto
      have "\<forall>n\<ge>N. \<bar>u n * v n - 0\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix n :: nat
        assume "n \<ge> N"
        have "\<bar>v n\<bar> < \<epsilon>/B"
          using \<open>N \<le> n\<close> hN by auto
        have "\<bar>u n * v n - 0\<bar> = \<bar>u n\<bar> * \<bar>v n\<bar>"
          by (simp add: abs_mult)
        also have "\<dots> \<le> B * \<bar>v n\<bar>"
          by (simp add: hB mult_right_mono)
        also have "\<dots> < B * (\<epsilon>/B)"
          using \<open>\<bar>v n\<bar> < \<epsilon>/B\<close> hBpos
          by (simp only: mult_strict_left_mono)
        also have "\<dots> = \<epsilon>"
          using \<open>B \<noteq> 0\<close> by simp
        finally show "\<bar>u n * v n - 0\<bar> < \<epsilon>"
          by this
      qed
      then show "\<exists>k. \<forall>n\<ge>k. \<bar>u n * v n - 0\<bar> < \<epsilon>"
        by (rule exI)
    qed
  qed
qed

end
