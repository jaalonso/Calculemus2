(* La_dama_o_el_tigre.thy
   La dama o el tigre.
   José A. Alonso Jiménez <https://jaalonso.github.io>
   Sevilla, 12-marzo-2020
   ================================================================== *)

(* ---------------------------------------------------------------------
   En el libro de Raymond Smullyan *\<questiondown>La dama o el tigre?* (en inglés,
   [The lady or the tiger?](https://books.google.es/books?id=v9zQ2jvETgAC))
   se plantea el siguiente  problema
      Un rey somete a un prisionero a la siguiente prueba: lo enfrenta a
      dos puertas, de las que el prisionero debe elegir una, y entrar la
      en habitación correspondiente. Se informa al prisionero que en
      cada una de las habitaciones puede haber un tigre o una dama. Como
      es natural, el prisionero debe elegir la puerta que le lleva a la
      dama (entre otras cosas, para no ser devorado por el tigre). Para
      ayudarle, en cada puerta hay un letrero. El de la puerta 1 dice
      "en esta habitación hay una dama y en la otra un tigre" y el de la
      puerta 2 dice "en una de estas habitaciones hay una dama y en una
      de estas habitaciones hay un tigre".

   Sabiendo que uno de los carteles dice la verdad y el otro no,
   demostrar que la dama se encuentra en la segunda habitación,
   completando la siguiente teoría
      theory La_dama_o_el_tigre
      imports Main
      begin

      lemma
        assumes "c1 \<longleftrightarrow> dp \<and> ts"
                "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
                "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
        shows   "ds"
        oops

      end
   donde se han usado los siguientes símbolos:
   + c1 que representa "el contenido del cartel de la puerta 1",
   + c2 que representa "el contenido del cartel de la puerta 2",
   + dp que representa "hay una dama en la primera habitación",
   + tp que representa "hay un tigre en la primera habitación",
   + ds que representa "hay una dama en la segunda habitación" y
   + ts que representa "hay un tigre en la segunda habitación".
   ------------------------------------------------------------------- *)

theory La_dama_o_el_tigre
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
          "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
          "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
  using assms
  by auto

(* 2\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
    "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
    "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
proof -
  note \<open>(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)\<close>
  then show "ds"
  proof
    assume "c1 \<and> \<not> c2"
    then have "c1" ..
    with \<open>c1 \<longleftrightarrow> dp \<and> ts\<close> have "dp \<and> ts" ..
    then have "(dp \<and> ts) \<or> (ds \<and> tp)" ..
    with assms(2) have "c2" ..
    have "\<not> c2" using \<open>c1 \<and> \<not> c2\<close> ..
    then show "ds" using \<open>c2\<close> ..
  next
    assume "c2 \<and> \<not> c1"
    then have "c2" ..
    with assms(2) have "(dp \<and> ts) \<or> (ds \<and> tp)" ..
    then show "ds"
    proof
      assume "dp \<and> ts"
      with assms(1) have c1 ..
      have "\<not> c1" using \<open>c2 \<and> \<not> c1\<close> ..
      then show ds using \<open>c1\<close> ..
    next
      assume "ds \<and> tp"
      then show ds ..
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
    "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
    "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
proof -
  note \<open>(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)\<close>
  then show "ds"
  proof (rule disjE)
    assume "c1 \<and> \<not> c2"
    then have "c1" by (rule conjunct1)
    with \<open>c1 \<longleftrightarrow> dp \<and> ts\<close> have "dp \<and> ts" by (rule iffD1)
    then have "(dp \<and> ts) \<or> (ds \<and> tp)" by (rule disjI1)
    with assms(2) have "c2" by (rule iffD2)
    have "\<not> c2" using \<open>c1 \<and> \<not> c2\<close> by (rule conjunct2)
    then show "ds" using \<open>c2\<close> by (rule notE)
  next
    assume "c2 \<and> \<not> c1"
    then have "c2" by (rule conjunct1)
    with assms(2) have "(dp \<and> ts) \<or> (ds \<and> tp)" by (rule iffD1)
    then show "ds"
    proof (rule disjE)
      assume "dp \<and> ts"
      with assms(1) have c1 by (rule iffD2)
      have "\<not> c1" using \<open>c2 \<and> \<not> c1\<close> by (rule conjunct2)
      then show ds using \<open>c1\<close> by (rule notE)
    next
      assume "ds \<and> tp"
      then show ds by (rule conjunct1)
    qed
  qed
qed

end
