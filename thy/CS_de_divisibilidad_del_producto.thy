(* CS_de_divisibilidad_del_producto.thy
-- Si m divide a n o a k, entonces m divide a nk.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-enero-2024
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si m divide a n o a k, entonces m divide a nk.
-- ------------------------------------------------------------------- *)

(*
Demostración en lenguaje natural
================================

Se demuestra por casos.

Caso 1: Supongamos que m ∣ n. Entonces, existe un a ∈ ℕ tal que
   n = ma
Por tanto,
   nk = (ma)k
      = m(ak)
que es divisible por m.

Caso 2: Supongamos que m ∣ k. Entonces, existe un b ∈ ℕ tal que
   k = mb
Por tanto,
   nk = n(mb)
      = m(nb)
que es divisible por m.
*)

(* Demostraciones con Isabelle/HOL
   =============================== *)

theory CS_de_divisibilidad_del_producto
  imports Main
begin

(* 1ª demostración *)
lemma 
  fixes n m k :: nat
  assumes "m dvd n ∨ m dvd k"
  shows "m dvd (n * k)"
using assms
proof
    assume "m dvd n"
    then obtain a where "n = m * a" by auto
    then have "n * k = m * (a * k)" by simp
    then show ?thesis by auto
  next
    assume "m dvd k"
    then obtain b where "k = m * b" by auto
    then have "n * k = m * (n * b)" by simp
    then show ?thesis by auto
qed

(* 2ª demostración *)
lemma 
  fixes n m k :: nat
  assumes "m dvd n ∨ m dvd k"
  shows "m dvd (n * k)"
  using assms by auto

end