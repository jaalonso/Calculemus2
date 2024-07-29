(* Pruebas_de_length_(repeat_x_n)_Ig_n.thy
-- Pruebas de length (replicate n x) = n
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 29-julio-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Lean están definidas length y replicate tales que
-- + (length xs) es la longitud de la lista xs. Por ejemplo,
--      length [1,2,5,2] = 4
-- + (replicate n n) es la lista que tiene el elemento x n veces. Por
--   ejemplo,
--      replicate 3 7 = [7, 7, 7]
--
-- Demostrar que
--    length (replicate n x) = n
-- ------------------------------------------------------------------ *)

theory "Pruebas_de_length_(repeat_x_n)_Ig_n"
imports Main
begin

(* 1\<ordfeminine> demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  have "length (replicate 0 x) = length ([] :: 'a list)"
    by (simp only: replicate.simps(1))
  also have "\<dots> = 0"
    by (rule list.size(3))
  finally show "length (replicate 0 x) = 0"
    by this
next
  fix n
  assume HI : "length (replicate n x) = n"
  have "length (replicate (Suc n) x) =
        length (x # replicate n x)"
    by (simp only: replicate.simps(2))
  also have "\<dots> = length (replicate n x) + 1"
    by (simp only: list.size(4))
  also have "\<dots> = Suc n"
    by (simp only: HI)
  finally show "length (replicate (Suc n) x) = Suc n"
    by this
qed

(* 2\<ordfeminine> demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  show "length (replicate 0 x) = 0"
    by simp
next
  fix n
  assume "length (replicate n x) = n"
  then show "length (replicate (Suc n) x) = Suc n"
    by simp
qed

(* 3\<ordfeminine> demostración⁾*)

lemma "length (replicate n x) = n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4\<ordfeminine> demostración⁾*)

lemma "length (replicate n x) = n"
  by (rule length_replicate)

end
