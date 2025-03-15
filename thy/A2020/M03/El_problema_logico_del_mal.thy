(* El_problema_logico_del_mal.thy
   El problema lógico del mal.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 5-marzo-2020
   ================================================================== *)

(* ---------------------------------------------------------------------
   El problema lógico​ del mal intenta demostrar la inconsistencia lógica
   entre la existencia de una entidad omnipotente, omnibenevolente y
   omnisciente y la existencia del mal. Se ha atribuido al filósofo
   griego Epicuro la formulación original del problema del mal y este
   argumento puede esquematizarse como sigue:
      Si Dios fuera capaz de evitar el mal y quisiera hacerlo, lo
      haría. Si Dios fuera incapaz de evitar el mal, no sería
      omnipotente; si no quisiera evitar el mal sería malévolo. Dios no
      evita el mal. Si Dios existe, es omnipotente y no es
      malévolo. Luego, Dios no existe.

   Demostrar con Isabelle/HOL la corrección del argumento completando la
   siguiente teoría
      theory El_problema_logico_del_mal
      imports Main
      begin

      lemma
        assumes "C \<and> Q \<longrightarrow> P"
                "\<not>C \<longrightarrow> \<not>Op"
                "\<not>Q \<longrightarrow> M"
                "\<not>P"
                "E \<longrightarrow> Op \<and> \<not>M"
        shows  "\<not>E"
        oops
      end
   donde se han usado los siguientes símbolos
   + C:  Dios es capaz de evitar el mal.
   + Q:  Dios quiere evitar el mal.
   + Op: Dios es omnipotente.
   + M:  Dios es malévolo.
   + P:  Dios evita el mal.
   + E:  Dios existe.
   ------------------------------------------------------------------- *)

theory El_problema_logico_del_mal
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma notnotI: "P \<Longrightarrow> \<not>\<not>P"
  by simp

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
  by simp

lemma
  assumes "C \<and> Q \<longrightarrow> P"
          "\<not>C \<longrightarrow> \<not>Op"
          "\<not>Q \<longrightarrow> M"
          "\<not>P"
          "E \<longrightarrow> Op \<and> \<not>M"
  shows  "\<not>E"
proof (rule notI)
  assume "E"
  with \<open>E \<longrightarrow> Op \<and> \<not>M\<close> have "Op \<and> \<not>M" by (rule mp)
  then have "Op" by (rule conjunct1)
  then have "\<not>\<not>Op" by (rule notnotI)
  with \<open>\<not>C \<longrightarrow> \<not>Op\<close> have "\<not>\<not>C" by (rule mt)
  then have "C" by (rule notnotD)
  moreover
  have "\<not>M" using \<open>Op \<and> \<not>M\<close> by (rule conjunct2)
  with \<open>\<not>Q \<longrightarrow> M\<close> have "\<not>\<not>Q" by (rule mt)
  then have "Q" by (rule notnotD)
  ultimately have "C \<and> Q" by (rule conjI)
  with \<open>C \<and> Q \<longrightarrow> P\<close> have "P" by (rule mp)
  with \<open>\<not>P\<close> show False by (rule notE)
qed

(* 2\<ordfeminine> demostración *)

lemma
  assumes "C \<and> Q \<longrightarrow> P"
          "\<not>C \<longrightarrow> \<not>Op"
          "\<not>Q \<longrightarrow> M"
          "\<not>P"
          "E \<longrightarrow> Op \<and> \<not>M"
  shows  "\<not>E"
using assms by blast

end
