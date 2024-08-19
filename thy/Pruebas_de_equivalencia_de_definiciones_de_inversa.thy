(* Pruebas_de_equivalencia_de_definiciones_de_inversa.thy
-- Pruebas de equivalencia de definiciones de inversa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-agosto-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Lean, está definida la función
--    rev :: "'a list \<Rightarrow> 'a list"
-- tal que (rev xs) es la lista obtenida invirtiendo el orden de los
-- elementos de xs. Por ejemplo,
--    rev  [3,2,5,1] = [1,5,2,3]
-- Su definición es
--    primrec rev :: "'a list \<Rightarrow> 'a list" where
--      "rev [] = []"
--    | "rev (x # xs) = rev xs @ [x]"
--
-- Una definición alternativa es
--    fun inversa_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
--      "inversa_aux [] ys     = ys"
--    | "inversa_aux (x#xs) ys = inversa_aux xs (x#ys)"
--
--    fun inversa :: "'a list \<Rightarrow> 'a list" where
--      "inversa xs = inversa_aux xs []"
--
-- Demostrar que las dos definiciones son equivalentes; es decir,
--    inversa xs = rev xs
-- ------------------------------------------------------------------ *)

theory Pruebas_de_equivalencia_de_definiciones_de_inversa
imports Main
begin

(* Definición alternativa *)
(* ====================== *)

fun inversa_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversa_aux [] ys     = ys"
| "inversa_aux (x#xs) ys = inversa_aux xs (x#ys)"

fun inversa :: "'a list \<Rightarrow> 'a list" where
  "inversa xs = inversa_aux xs []"

(* Lema auxiliar: inversa_aux xs ys = (rev xs) @ ys *)
(* ================================================ *)

(* 1\<ordfeminine> demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys"
    by (simp only: inversa_aux.simps(1))
  also have "\<dots> = [] @ ys"
    by (simp only: append.simps(1))
  also have "\<dots> = rev [] @ ys"
    by (simp only: rev.simps(1))
  finally show "inversa_aux [] ys = rev [] @ ys"
    by this
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. inversa_aux xs ys = rev xs@ys"
  show "\<And>ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)"
      by (simp only: inversa_aux.simps(2))
    also have "\<dots> = rev xs@(a#ys)"
      by (simp only: HI)
    also have "\<dots> = rev xs @ ([a] @ ys)"
      by (simp only: append.simps)
    also have "\<dots> = (rev xs @ [a]) @ ys"
      by (simp only: append_assoc)
    also have "\<dots> = rev (a # xs) @ ys"
      by (simp only: rev.simps(2))
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys"
      by this
  qed
qed

(* 2\<ordfeminine> demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  have "inversa_aux [] ys = ys" by simp
  also have "\<dots> = [] @ ys" by simp
  also have "\<dots> = rev [] @ ys" by simp
  finally show "inversa_aux [] ys = rev [] @ ys" .
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. inversa_aux xs ys = rev xs@ys"
  show "\<And>ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = inversa_aux xs (a#ys)" by simp
    also have "\<dots> = rev xs@(a#ys)" using HI by simp
    also have "\<dots> = rev xs @ ([a] @ ys)" by simp
    also have "\<dots> = (rev xs @ [a]) @ ys" by simp
    also have "\<dots> = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 3\<ordfeminine> demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  fix ys :: "'a list"
  show "inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume HI: "\<And>ys. inversa_aux xs ys = rev xs@ys"
  show "\<And>ys. inversa_aux (a#xs) ys = rev (a#xs)@ys"
  proof -
    fix ys
    have "inversa_aux (a#xs) ys = rev xs@(a#ys)" using HI by simp
    also have "\<dots> = rev (a # xs) @ ys" by simp
    finally show "inversa_aux (a#xs) ys = rev (a#xs)@ys" .
  qed
qed

(* 4\<ordfeminine> demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  show "\<And>ys. inversa_aux [] ys = rev [] @ ys" by simp
next
  fix a ::'a and xs :: "'a list"
  assume "\<And>ys. inversa_aux xs ys = rev xs@ys"
  then show "\<And>ys. inversa_aux (a#xs) ys = rev (a#xs)@ys" by simp
qed

(* 5\<ordfeminine> demostración del lema auxiliar *)
lemma
  "inversa_aux xs ys = (rev xs) @ ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

(* 6\<ordfeminine> demostración del lema auxiliar *)
lemma inversa_equiv:
  "inversa_aux xs ys = (rev xs) @ ys"
by (induct xs arbitrary: ys) simp_all

(* Demostraciones del lema principal *)
(* ================================= *)

(* 1\<ordfeminine> demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"
    by (rule inversa.simps)
  also have "\<dots> = (rev xs) @ []"
    by (rule inversa_equiv)
  also have "\<dots> = rev xs"
    by (rule append.right_neutral)
  finally show "inversa xs = rev xs"
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma "inversa xs = rev xs"
proof -
  have "inversa xs = inversa_aux xs []"  by simp
  also have "\<dots> = (rev xs) @ []" by (rule inversa_equiv)
  also have "\<dots> = rev xs" by simp
  finally show "inversa xs = rev xs" .
qed

(* 3\<ordfeminine> demostración *)
lemma "inversa xs = rev xs"
by (simp add: inversa_equiv)

end
