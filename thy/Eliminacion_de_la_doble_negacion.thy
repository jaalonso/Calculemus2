(* Eliminacion_de_la_doble_negacion.thy
-- \<not>\<not>P \<rightarrow> P.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    \<not>\<not>P \<rightarrow> P
-- ------------------------------------------------------------------- *)

(*
Demostración en lenguaje natural
================================

Supongamos que
   \<not>\<not>P                                                            (1)

Por el principio del tercio excluso, se tiene
   P \<or> \<not>P
lo que da lugar a dos casos.

En el primer caso, se supone P que es lo que hay que demostrar.

En el primer caso, se supone \<not>P que es una contradicción con (1).
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory Eliminacion_de_la_doble_negacion
  imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "\<not>\<not>P \<longrightarrow> P"
proof 
  assume h1 : "\<not>\<not>P"
  have "\<not>P \<or> P" by (rule excluded_middle)
  then show "P"
  proof
    assume "\<not>P"
    then show "P" using h1 by (simp only: notE)
  next
    assume "P"
    then show "P" .
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "\<not>\<not>P \<longrightarrow> P"
proof 
  assume h1 : "\<not>\<not>P"
  show "P"
  proof (rule ccontr)
    assume "\<not>P"
    then show False using h1 by simp
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "\<not>\<not>P \<longrightarrow> P"
  by simp

end