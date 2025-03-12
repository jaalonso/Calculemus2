theory reto

imports Main
begin

(* 1ª solución *)

lemma "∀(f :: bool ⇒ bool). f (f (f b)) = f b"
  by smt

(* 2ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by smt

(* 3ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by (cases b; cases "f True"; cases "f False"; simp)

(* 4ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› by simp
next
  assume "f True" "f False" "¬ b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹f False› ‹¬ b› by simp
next
  assume "f True" "¬ f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹¬ f False› ‹b› by simp
next
  assume "f True" "¬ f False" "¬ b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹¬ f False› ‹¬ b› by simp
next
  assume "¬ f True" "f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹f False› ‹b› by simp
next
  assume "¬ f True" "f False" "¬ b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹f False› ‹¬ b› by simp
next
  assume "¬ f True" "¬ f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹¬ f False› ‹b› by simp
next
  assume "¬ f True" "¬ f False" "¬ b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹¬ f False› ‹¬b› by simp
qed

(* 5ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f True)" using ‹f True› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "f True" "f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f True)" using ‹f False› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f False" using ‹f True› ‹f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "f True" "¬ f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f True)" using ‹f True› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "f True" "¬ f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f False)" using ‹¬ f False› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "¬ f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f False)" using ‹¬ f True› by simp
  also have "… = f True" using ‹f False› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "¬ f True" "f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f True)" using ‹f False› by simp
  also have "… = f False" using ‹¬ f True› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "¬ f True" "¬ f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f False)" using ‹¬ f True› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = False" using ‹¬ f False› by simp
  also have "… = f True" using ‹¬ f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this
next
  assume "¬ f True" "¬ f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f False)" using ‹¬ f False› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this
qed

(* 6ª solución *)

theorem
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
proof (cases b)
  assume b: b
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
      using b ft by auto
  next
    assume ft: "¬ f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
next
  assume b: "¬ b"
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  next
    assume ft: "¬ f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
qed

(* 7ª solución *)

theorem
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by (cases b "f True" "f False"
      rule: bool.exhaust [ case_product bool.exhaust
                         , case_product bool.exhaust])
    auto

end
