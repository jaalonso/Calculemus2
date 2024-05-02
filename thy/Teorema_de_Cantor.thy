(* Teorema_de_Cantor.thy
-- Teorema de Cantor
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-mayo-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar el teorema de Cantor:
--    \<forall> f : \<alpha> \<rightarrow> set \<alpha>, \<not> surjective f
-- ------------------------------------------------------------------ *)

theory Teorema_de_Cantor
imports Main
begin

(* 1\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i \<notin> f i}"
  have "\<exists> j. ?S = f j"
    using \<open>surj f\<close> by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  show False
  proof (cases "j \<in> ?S")
    assume "j \<in> ?S"
    then have "j \<notin> f j"
      by (rule CollectD)
    moreover
    have "j \<in> f j"
      using \<open>?S = f j\<close> \<open>j \<in> ?S\<close> by (rule subst)
    ultimately show False
      by (rule notE)
  next
    assume "j \<notin> ?S"
    with \<open>?S = f j\<close> have "j \<notin> f j"
      by (rule subst)
    then have "j \<in> ?S"
      by (rule CollectI)
    with \<open>j \<notin> ?S\<close> show False
      by (rule notE)
  qed
qed

(* 2\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i \<notin> f i}"
  have "\<exists> j. ?S = f j"
    using \<open>surj f\<close> by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j \<notin> ?S"
  proof (rule notI)
    assume "j \<in> ?S"
    then have "j \<notin> f j"
      by (rule CollectD)
    with \<open>?S = f j\<close> have "j \<notin> ?S"
      by (rule ssubst)
    then show False
      using \<open>j \<in> ?S\<close> by (rule notE)
  qed
  moreover
  have "j \<in> ?S"
  proof (rule CollectI)
    show "j \<notin> f j"
    proof (rule notI)
      assume "j \<in> f j"
      with \<open>?S = f j\<close> have "j \<in> ?S"
        by (rule ssubst)
      then have "j \<notin> f j"
        by (rule CollectD)
      then show False
        using \<open>j \<in> f j\<close> by (rule notE)
    qed
  qed
  ultimately show False
    by (rule notE)
qed

(* 3\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
proof
  assume "surj f"
  let ?S = "{i. i \<notin> f i}"
  have "\<exists> j. ?S = f j" using \<open>surj f\<close> by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j \<notin> ?S"
  proof
    assume "j \<in> ?S"
    then have "j \<notin> f j" by simp
    with \<open>?S = f j\<close> have "j \<notin> ?S" by simp
    then show False using \<open>j \<in> ?S\<close> by simp
  qed
  moreover
  have "j \<in> ?S"
  proof
    show "j \<notin> f j"
    proof
      assume "j \<in> f j"
      with \<open>?S = f j\<close> have "j \<in> ?S" by simp
      then have "j \<notin> f j" by simp
      then show False using \<open>j \<in> f j\<close> by simp
    qed
  qed
  ultimately show False by simp
qed

(* 4\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i \<notin> f i}"
  have "\<exists> j. ?S = f j"
    using \<open>surj f\<close> by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j \<in> ?S = (j \<notin> f j)"
    by (rule mem_Collect_eq)
  also have "\<dots> = (j \<notin> ?S)"
    by (simp only: \<open>?S = f j\<close>)
  finally show False
    by (simp only: simp_thms(10))
qed

(* 5\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
proof
  assume "surj f"
  let ?S = "{i. i \<notin> f i}"
  have "\<exists> j. ?S = f j" using \<open>surj f\<close> by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j \<in> ?S = (j \<notin> f j)" by simp
  also have "\<dots> = (j \<notin> ?S)" using \<open>?S = f j\<close> by simp
  finally show False by simp
qed

(* 6\<ordfeminine> demostración *)

theorem
  fixes f :: "'\<alpha> \<Rightarrow> '\<alpha> set"
  shows "\<not> surj f"
  unfolding surj_def
  by best

end
