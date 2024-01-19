(* Implicacion_mediante_disyuncion_y_negacion.thy
-- (P \<rightarrow> Q) \<leftrightarrow> \<not>P \<or> Q
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    (P \<rightarrow> Q) \<leftrightarrow> \<not>P \<or> Q
-- ------------------------------------------------------------------- *)

(* Demostración en lenguaje natural
   ================================ *)

(*
Demostraremos cada una de las implicaciones.

(==>) Supongamos que P \<rightarrow> Q. Distinguimos dos subcasos según el valor de
P.

Primer subcaso: suponemos P. Entonces. tenemos Q (por P \<rightarrow> Q) y. por
tanto, \<not>P \<or> Q.

Segundo subcaso: suponemos \<not>P. Entonces. tenemos \<not>P \<or> Q.

(<==) Supongamos que \<not>P \<or> Q y P y tenemos que demostrar
Q. Distinguimos dos subcasos según \<not>P \<or> Q.

Primer subcaso: Suponemos \<not>P. Entonces tenemos una contradicción con
P.

Segundo subcaso: Suponemos Q, que es lo que tenemos que demostrar.
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory Implicacion_mediante_disyuncion_y_negacion
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not>P \<or> Q)"
proof
  assume "P \<longrightarrow> Q"
  show "\<not>P \<or> Q" 
  proof -
    have "\<not>P \<or> P" by (rule excluded_middle)
    then show "\<not>P \<or> Q"
    proof (rule disjE)
      assume "\<not>P"
      then show "\<not>P \<or> Q" by (rule disjI1) 
    next  
      assume 2: "P"
      with `P \<longrightarrow> Q` have "Q" by (rule mp)
      then show "\<not>P \<or> Q" by (rule disjI2) 
    qed
  qed
next
  assume "\<not>P \<or> Q"
  show "P \<longrightarrow> Q"
  proof 
    assume "P"
    note `\<not>P \<or> Q`
    then show "Q"
    proof (rule disjE)
      assume "\<not>P"
      then show Q using `P` by (rule notE)
    next
      assume "Q"
      then show "Q" by this
    qed
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not>P \<or> Q)"
proof
  assume "P \<longrightarrow> Q"
  show "\<not>P \<or> Q" 
  proof -
    have "\<not>P \<or> P" by (rule excluded_middle)
    then show "\<not>P \<or> Q"
    proof 
      assume "\<not>P"
      then show "\<not>P \<or> Q" .. 
    next  
      assume 2: "P"
      with `P \<longrightarrow> Q` have "Q" ..
      then show "\<not>P \<or> Q" .. 
    qed
  qed
next
  assume "\<not>P \<or> Q"
  show "P \<longrightarrow> Q"
  proof 
    assume "P"
    note `\<not>P \<or> Q`
    then show "Q"
    proof 
      assume "\<not>P"
      then show Q using `P` ..
    next
      assume "Q"
      then show "Q" .
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not>P \<or> Q)"
  by simp

end