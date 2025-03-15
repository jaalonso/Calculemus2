(* Praeclarum_theorema.thy
-- Praeclarum theorema
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Seville, January 21, 2025
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Prove the [praeclarum theorema](https://tinyurl.com/25yt3ef9) of
-- Leibniz:
--    (p \<rightarrow> q) \<and> (r \<rightarrow> s) \<rightarrow> ((p \<and> r) \<rightarrow> (q \<and> s))
-- ------------------------------------------------------------------ *)

theory Praeclarum_theorema
imports Main
begin

(* Proof 1 *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof (rule impI)
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof (rule impI)
    assume "p \<and> r"
    show "q \<and> s"
    proof (rule conjI)
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct1)
      moreover have "p" using \<open>p \<and> r\<close> by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct2)
      moreover have "r" using \<open>p \<and> r\<close> by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

(* Proof 2 *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof
    assume "p \<and> r"
    show "q \<and> s"
    proof
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "p" using \<open>p \<and> r\<close> ..
      ultimately show "q" ..
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "r" using \<open>p \<and> r\<close> ..
      ultimately show "s" ..
    qed
  qed
qed

(* Proof 3 *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* Proof 4 *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  by simp

end
