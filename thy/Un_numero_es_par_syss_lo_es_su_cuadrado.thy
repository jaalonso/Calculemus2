(* Un_numero_es_par_syss_lo_es_su_cuadrado.lean
-- Un número es par si y solo si lo es su cuadrado
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que un número es par si y solo si lo es su cuadrado.
-- ------------------------------------------------------------------ *)

theory Un_numero_es_par_syss_lo_es_su_cuadrado
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  fixes n :: int
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
proof (rule iffI)
  assume "even (n\<^sup>2)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n\<^sup>2 = 2*(2*k*(k+1))+1"
    proof -
      have "n\<^sup>2 = (2*k+1)\<^sup>2"
        by (simp add: \<open>n = 2 * k + 1\<close>)
      also have "\<dots> = 4*k\<^sup>2+4*k+1"
        by algebra
      also have "\<dots> = 2*(2*k*(k+1))+1"
        by algebra
      finally show "n\<^sup>2 = 2*(2*k*(k+1))+1" .
    qed
    then have "\<exists>k'. n\<^sup>2 = 2*k'+1"
      by (rule exI)
    then have "odd (n\<^sup>2)"
      by fastforce
    then show False
      using \<open>even (n\<^sup>2)\<close> by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n\<^sup>2 = 2*(2*k\<^sup>2)"
    by simp
  then show "even (n\<^sup>2)"
    by simp
qed

(* 2\<ordfeminine> demostración *)

lemma
  fixes n :: int
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
proof
  assume "even (n\<^sup>2)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n\<^sup>2 = 2*(2*k*(k+1))+1"
      by algebra
    then have "odd (n\<^sup>2)"
      by simp
    then show False
      using \<open>even (n\<^sup>2)\<close> by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n\<^sup>2 = 2*(2*k\<^sup>2)"
    by simp
  then show "even (n\<^sup>2)"
    by simp
qed

(* 3\<ordfeminine> demostración *)

lemma
  fixes n :: int
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
proof -
  have "even (n\<^sup>2) = (even n \<and> (0::nat) < 2)"
    by (simp only: even_power)
  also have "\<dots> = (even n \<and> True)"
    by (simp only: less_numeral_simps)
  also have "\<dots> = even n"
    by (simp only: HOL.simp_thms(21))
  finally show "even (n\<^sup>2) \<longleftrightarrow> even n"
    by this
qed

(* 4\<ordfeminine> demostración *)

lemma
  fixes n :: int
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
proof -
  have "even (n\<^sup>2) = (even n \<and> (0::nat) < 2)"
    by (simp only: even_power)
  also have "\<dots> = even n"
    by simp
  finally show "even (n\<^sup>2) \<longleftrightarrow> even n" .
qed

(* 5\<ordfeminine> demostración *)

lemma
  fixes n :: int
  shows "even (n\<^sup>2) \<longleftrightarrow> even n"
  by simp

end
