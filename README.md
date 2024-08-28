This repository contains the solutions in Lean4 and Isabelle/HOL for the
exercises proposed in the [Calculemus](https://jaalonso.github.io/calculemus) blog.

The solutions have been verified with the [version 4.11.0-rc2](https://github.com/leanprover/lean4/releases/tag/v4.11.0-rc2) of Lean.


# Latest exercises

-   [Proofs of "flatten (mirror a) = reverse (flatten a)"](./textos/Flatten_of_mirror.md) (In [Lean4](./src/Flatten_of_mirror.lean) and [Isabelle](./thy/Flatten_of_mirror.thy)).
-   [Proofs that the mirror function of binary trees is involutive](https://jaalonso.github.io/calculemus/posts/2024/08/26-proofs_that_the_mirror_function_of_binary_trees_is_involutive) (In [Lean4](./src/Proofs_that_the_mirror_function_of_binary_trees_is_involutive.lean) and [Isabelle](./thy/Proofs_that_the_mirror_function_of_binary_trees_is_involutive.thy)).
-   [Equivalence of reverse definitions](https://jaalonso.github.io/calculemus/posts/2024/08/19-equivalence_of_reverse_definitions/) (In [Lean](./src/Equivalence_of_reverse_definitions.lean) and [Isabelle](./thy/Equivalence_of_reverse_definitions.thy)).
-   [Proofs of "take n xs ++ drop n xs = xs"](https://jaalonso.github.io/calculemus/posts/2024/08/14-proofs_of_take_n_xs_%2B%2B_drop_n_xs_eq_xs/) (In [Lean](./src/Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs.lean) and [Isabelle](./thy/Proofs_of_take_n_xs_++_drop_n_xs_Eq_xs.thy)).
-   [Proofs of the equality "length(xs ++ ys) = length(xs) + length(ys)"](https://jaalonso.github.io/calculemus/posts/2024/08/07-proofs_of_the_equality_lengthxs%2B%2Bys_eq_lengthxs%2Blengthys) (In [Lean](./src/Proofs_of_the_equality_length(xs++ys)_Eq_length(xs)+length(ys).lean) and [Isabelle](./thy/Proofs_of_the_equality_length(xs++ys)_Eq_length(xs)+length(ys).thy)).
-   [Asociatividad de la concatenación de listas](./textos/Asociatividad_de_la_concatenacion_de_listas.md) (En [Lean](./src/Asociatividad_de_la_concatenacion_de_listas.lean) y en [Isabelle](./thy/Asociatividad_de_la_concatenacion_de_listas.thy)).
-   [Pruebas de "length (replicate n x) = n"](./textos/Pruebas_de_length_(repeat_x_n)_Ig_n.md) (En [Lean](./src/Pruebas_de_length_(repeat_x_n)_Ig_n.lean) y en [Isabelle](./thy/Pruebas_de_length_(repeat_x_n)_Ig_n.thy)).
-   [Si u es una sucesión no decreciente y su límite es a, entonces u(n) ≤ a para todo n](./textos/Limite_de_sucesiones_no_decrecientes.md) (En [Lean](./src/Limite_de_sucesiones_no_decrecientes.lean) y en [Isabelle](./thy/Limite_de_sucesiones_no_decrecientes.thy)).
-   [Las sucesiones divergentes positivas no tienen límites finitos](./textos/Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.md) (En [Lean](./src/Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.lean) y en [Isabelle](./thy/Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.thy)).
-   [Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u](./textos/Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.md) (En [Lean](./src/Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.lean) y en [Isabelle](./thy/Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.thy)).
-   [El punto de acumulación de las sucesiones convergente es su límite](./textos/El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.md) (En [Lean](./src/El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.lean) y en [Isabelle](./thy/El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.thy)).
-   [Las subsucesiones tienen el mismo límite que la sucesión](./textos/Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.md) (En [Lean](./src/Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean) y en [Isabelle](./thy/Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.thy)).
-   [Si a es un punto de acumulación de u, entonces (∀ε>0)(∀n∈ℕ)(∃k≥n)[u(k)−a| < ε]​](./textos/Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.md) (En [Lean](./src/Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.lean) y en [Isabelle](./thy/Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.thy)).
-   [Las funciones de extracción no están acotadas](./textos/Las_funciones_de_extraccion_no_estan_acotadas.md) (En [Lean](./src/Las_funciones_de_extraccion_no_estan_acotadas.lean) y en [Isabelle](./thy/Las_funciones_de_extraccion_no_estan_acotadas.thy)).
-   [Relación entre los índices de las subsucesiones y de la sucesión](./textos/Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.md) (En [Lean](./src/Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.lean) y en [Isabelle](./thy/Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.thy)).
-   [Las particiones definen relaciones de equivalencia](./textos/Las_particiones_definen_relaciones_de_equivalencia.md) (En [Lean](./src/Las_particiones_definen_relaciones_de_equivalencia.lean) y en [Isabelle](./thy/Las_particiones_definen_relaciones_de_equivalencia.thy)).
-   [Las particiones definen relaciones transitivas](./textos/Las_particiones_definen_relaciones_transitivas.md) (En [Lean](./src/Las_particiones_definen_relaciones_transitivas.lean) y en [Isabelle](./thy/Las_particiones_definen_relaciones_transitivas.thy)).
-   [Las familias de conjuntos definen relaciones simétricas](./textos/Las_familias_de_conjuntos_definen_relaciones_simetricas.md) (En [Lean](./src/Las_familias_de_conjuntos_definen_relaciones_simetricas.lean) y en [Isabelle](./thy/Las_familias_de_conjuntos_definen_relaciones_simetricas.thy)).
-   [Las particiones definen relaciones reflexivas](./textos/Las_particiones_definen_relaciones_reflexivas.md) (En [Lean](./src/Las_particiones_definen_relaciones_reflexivas.lean) y en [Isabelle](./thy/Las_particiones_definen_relaciones_reflexivas.thy)).
-   [El conjunto de las clases de equivalencia es una partición](./textos/El_conjunto_de_las_clases_de_equivalencia_es_una_particion.md) (En [Lean](./src/El_conjunto_de_las_clases_de_equivalencia_es_una_particion.lean) y en [Isabelle](./thy/El_conjunto_de_las_clases_de_equivalencia_es_una_particion.thy)).
-   [Las clases de equivalencia de elementos no relacionados son disjuntas](./textos/Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.md) (En [Lean](./src/Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.lean) y en [Isabelle](./thy/Las_clases_de_equivalencia_de_elementos_no_relacionados_son_disjuntas.thy)).
-   [Las clases de equivalencia de elementos relacionados son iguales](./textos/Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.md) (En [Lean](./src/Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.lean) y en [Isabelle](./thy/Las_clases_de_equivalencia_de_elementos_relacionados_son_iguales.thy)).
-   [Las sucesiones convergentes son sucesiones de Cauchy](./textos/Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.md) (En [Lean](./src/Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.lean) y en [Isabelle](./thy/Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.thy)).
-   [La composición por la izquierda con una inyectiva es una operación inyectiva](./textos/La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.md) (En [Lean](./src/La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean) y en [Isabelle](./thy/La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.thy)).
-   [La igualdad de valores es una relación de equivalencia](./textos/La_igualdad_de_valores_es_una_relacion_de_equivalencia.md) (En [Lean](./src/La_igualdad_de_valores_es_una_relacion_de_equivalencia.lean) y en [Isabelle](./thy/La_igualdad_de_valores_es_una_relacion_de_equivalencia.thy)).
-   [La equipotencia es una relación de equivalencia](./textos/La_equipotencia_es_una_relacion_de_equivalencia.md) (En [Lean](./src/La_equipotencia_es_una_relacion_de_equivalencia.lean) y en [Isabelle](./thy/La_equipotencia_es_una_relacion_de_equivalencia.thy)).
-   [La equipotencia es una relación transitiva](./textos/La_equipotencia_es_una_relacion_transitiva.md) (En [Lean](./src/La_equipotencia_es_una_relacion_transitiva.lean) y en [Isabelle](./thy/La_equipotencia_es_una_relacion_transitiva.thy)).


# Old exercises


## Demostraciones de una propiedad de los números enteros

-   [∀ m n ∈ ℕ, Even n → Even (m \* n)](./textos/El_producto_por_un_par_es_par.md) (En [Lean4](./src/El_producto_por_un_par_es_par.lean)).


## Propiedades elementales de los números reales

-   [En ℝ, (ab)c = b(ac)](./textos/Asociativa_conmutativa_de_los_reales.md) (En [Lean4](./src/Asociativa_conmutativa_de_los_reales.lean)).
-   [En ℝ, (cb)a = b(ac)](./textos/(cb)a_eq_b(ac).md) (En [Lean4](./src/(cb)a_eq_b(ac).lean)).
-   [En ℝ, a(bc) = b(ac)](./textos/a(bc)_eq_b(ac).md) (En [Lean4](./src/a(bc)_eq_b(ac).lean)).
-   [En ℝ, si ab = cd y e = f, entonces a(be) = c(df)](./textos/a(be)_eq_c(df).md) (En [Lean4](./src/a(be)_eq_c(df).lean)).
-   [En ℝ, si bc = ef, entonces ((ab)c)d = ((ae)f)d](./textos/Si_bc_eq_ef_entonces_((ab)c)d_eq_((ae)f)d.md) (En [Lean4](./src/Si_bc_eq_ef_entonces_((ab)c)d_eq_((ae)f)d.lean)).
-   [En ℝ, si c = ba-d y d = ab, entonces c = 0](./textos/Si_c_eq_ba-d_y_d_eq_ab_entonces_c_eq_0.md) (En [Lean4](./src/Si_c_eq_ba-d_y_d_eq_ab_entonces_c_eq_0.lean)).
-   [En ℝ, (a+b)(a+b) = aa+2ab+bb](./textos/(a+b)(a+b)_eq_aa+2ab+bb.md) (En [Lean4](./src/(a+b)(a+b)_eq_aa+2ab+bb.lean)).
-   [En ℝ, (a+b)(c+d) = ac+ad+bc+bd](./textos/(a+b)(c+d)_eq_ac+ad+bc+bd.md) (En [Lean4](./src/(a+b)(c+d)_eq_ac+ad+bc+bd.lean)).
-   [En ℝ, (a+b)(a-b) = a<sup>2</sup>-b<sup>2</sup>](./textos/(a+b)(a-b)_eq_aa-bb.md) (En [Lean4](./src/(a+b)(a-b)_eq_aa-bb.lean)).
-   [En ℝ, si c = da+b y b = ad, entonces c = 2ad](./textos/Si_c_eq_da+b_y_b_eq_ad_entonces_c_eq_2ad.md) (En [Lean4](./src/Si_c_eq_da+b_y_b_eq_ad_entonces_c_eq_2ad.lean)).
-   [En ℝ, si a+b = c, entonces (a+b)(a+b) = ac+bc](./textos/Sia+b_eq_c_entonces_(a+b)(a+b)_eq_ac+bc.md) (En [Lean4](./src/Sia+b_eq_c_entonces_(a+b)(a+b)_eq_ac+bc.lean)).
-   [Si x e y son sumas de dos cuadrados, entonces xy también lo es](./textos/Producto_de_suma_de_cuadrados.md) (En [Lean4](./src/Producto_de_suma_de_cuadrados.lean)).
-   [En ℝ, x² + y² = 0 ↔ x = 0 ∧ y = 0](./textos/Suma_nula_de_dos_cuadrados.md) (En [Lean4](./src/Suma_nula_de_dos_cuadrados.lean)).
-   [En ℝ, x² = 1 → x = 1 ∨ x = -1](./textos/Cuadrado_igual_a_uno.md) (En [Lean4](./src/Cuadrado_igual_a_uno.lean)).
-   [En ℝ, x² = y² → x = y ∨ x = -y](./textos/Cuadrado_igual_a_cuadrado.md) (En [Lean4](./src/Cuadrado_igual_a_cuadrado.lean)).
-   [En ℝ, |a| = |a - b + b|](./textos/Demostracion_por_congruencia.md) (En [Lean4](./src/Demostracion_por_congruencia.lean)).


## Propiedades elementales de los monoides

-   [En los monoides, los inversos a la izquierda y a la derecha son iguales](./textos/En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.md) (En [Lean](./src/En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.lean) y en [Isabelle](./thy/En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.thy)).
-   [Producto de potencias de la misma base en monoides](./textos/Producto_de_potencias_de_la_misma_base_en_monoides.md) (En [Lean](./src/Producto_de_potencias_de_la_misma_base_en_monoides.lean) y en [Isabelle](./thy/Producto_de_potencias_de_la_misma_base_en_monoides.thy)).
-   [Equivalencia de inversos iguales al neutro](./textos/Equivalencia_de_inversos_iguales_al_neutro.md) (En [Lean](./src/Equivalencia_de_inversos_iguales_al_neutro.lean) y en [Isabelle](./thy/Equivalencia_de_inversos_iguales_al_neutro.thy)).
-   [Unicidad de inversos en monoides](./textos/Unicidad_de_inversos_en_monoides.md) (En [Lean](./src/Unicidad_de_inversos_en_monoides.lean) y en [Isabelle](./thy/Unicidad_de_inversos_en_monoides.thy)).
-   [Caracterización de producto igual al primer factor](./textos/Caracterizacion_de_producto_igual_al_primer_factor.md) (En [Lean](./src/Caracterizacion_de_producto_igual_al_primer_factor.lean) y en [Isabelle](./thy/Caracterizacion_de_producto_igual_al_primer_factor.thy)).
-   [Si M es un monoide, a ∈ M y m, n ∈ ℕ, entonces a<sup>(m·n)</sup> = (a<sup>m</sup>)<sup>n</sup>](./textos/Potencias_de_potencias_en_monoides.md) (En [Lean](./src/Potencias_de_potencias_en_monoides.lean) y en [Isabelle](./thy/Potencias_de_potencias_en_monoides.thy)).
-   [Los monoides booleanos son conmutativos](./textos/Los_monoides_booleanos_son_conmutativos.md) (En [Lean](./src/Los_monoides_booleanos_son_conmutativos.lean) y en [Isabelle](./thy/Los_monoides_booleanos_son_conmutativos.thy)).


## Propiedades elementales de los grupos

-   [Unicidad del elemento neutro en los grupos](./textos/Unicidad_del_elemento_neutro_en_los_grupos.md) (En [Lean](./src/Unicidad_del_elemento_neutro_en_los_grupos.lean) y en [Isabelle](./thy/Unicidad_del_elemento_neutro_en_los_grupos.thy)).
-   [Si G es un grupo y a ∈ G, entonces aa⁻¹ = 1](./textos/Producto_por_inverso.md) (En [Lean4](./src/Producto_por_inverso.lean)).
-   [Si G es un grupo y a ∈ G, entonces a·1 = a](./textos/Producto_por_uno.md) (En [Lean4](./src/Producto_por_uno.lean)).
-   [Si G es un grupo y a, b ∈ G tales que ab = 1 entonces a⁻¹ = b](./textos/Unicidad_de_los_inversos_en_los_grupos.md) (En [Lean](./src/Unicidad_de_los_inversos_en_los_grupos.lean) y en [Isabelle](./thy/Unicidad_de_los_inversos_en_los_grupos.thy)).
-   [Si G es un grupo y a, b ∈ G, entonces (ab)⁻¹ = b⁻¹a⁻¹](./textos/Inverso_del_producto.md) (En [Lean](./src/Inverso_del_producto.lean) y en [Isabelle](./thy/Inverso_del_producto.thy)).
-   [Si G un grupo y a ∈ G, entonces (a⁻¹)⁻¹ = a](./textos/Inverso_de_inverso_en_grupos.md) (En [Lean](./src/Inverso_del_inverso_en_grupos.lean) y en [Isabelle](./thy/Inverso_del_inverso_en_grupos.thy)).
-   [Si G es un grupo y a, b, c ∈ G tales que a·b = a·c, entonces b = c](./textos/Propiedad_cancelativa_en_grupos.md) (En [Lean](./src/Propiedad_cancelativa_en_grupos.lean) y en [Isabelle](./thy/Propiedad_cancelativa_en_grupos.thy)).


## Propiedades elementales de los anillos

-   [Si R es un anillo y a ∈ R, entonces a + 0 = a](./textos/Suma_con_cero.md) (En [Lean4](./src/Suma_con_cero.lean)).
-   [Si R es un anillo y a ∈ R, entonces a + -a = 0](./textos/Suma_con_opuesto.md) (En [Lean4](./src/Suma_con_opuesto.lean)).
-   [Si R es un anillo y a, b ∈ R, entonces -a + (a + b) = b](./textos/Opuesto_se_cancela_con_la_suma_por_la_izquierda.md) (En [Lean4](./src/Opuesto_se_cancela_con_la_suma_por_la_izquierda.lean)).
-   [Si R es un anillo y a, b ∈ R, entonces (a + b) + -b = a](./textos/Opuesto_se_cancela_con_la_suma_por_la_derecha.md) (En [Lean4](./src/Opuesto_se_cancela_con_la_suma_por_la_derecha.lean)).
-   [Si R es un anillo y a, b, c ∈ R tales que a+b=a+c, entonces b=c](./textos/Cancelativa_izquierda.md) (En [Lean4](./src/Cancelativa_izquierda.lean)).
-   [Si R es un anillo y a, b, c ∈ R tales que a+b=c+b, entonces a=c](./textos/Cancelativa_derecha.md) (En [Lean4](./src/Cancelativa_derecha.lean)).
-   [Si R es un anillo y a ∈ R, entonces a.0 = 0](./textos/Multiplicacion_por_cero.md) (En [Lean4](./src/Multiplicacion_por_cero.lean)).
-   [Si R es un anillo y a ∈ R, entonces 0.a = 0](./textos/Multiplicacion_por_cero_izquierda.md) (En [Lean4](./src/Multiplicacion_por_cero_izquierda.lean)).
-   [Si R es un anillo y a, b ∈ R tales que a+b=0, entonces -a=b](./textos/Opuesto_ig_si_suma_ig_cero.md) (En [Lean4](./src/Opuesto_ig_si_suma_ig_cero.lean)).
-   [Si R es un anillo y a, b ∈ R tales que a+b=0, entonces a=-b](./textos/Ig_opuesto_si_suma_ig_cero.md) (En [Lean4](./src/Ig_opuesto_si_suma_ig_cero.lean)).
-   [Si R es un anillo, entonces -0 = 0](./textos/Opuesto_del_cero.md) (En [Lean4](./src/Opuesto_del_cero.lean)).
-   [Si R es un anillo y a ∈ R, entonces -(-a) = a](./textos/Opuesto_del_opuesto.md) (En [Lean4](./src/Opuesto_del_opuesto.lean)).
-   [Si R es un anillo y a, b ∈ R, entonces a - b = a + -b](./textos/Resta_igual_suma_opuesto.md) (En [Lean4](./src/Resta_igual_suma_opuesto.lean)).
-   [Si R es un anillo y a ∈ R, entonces a - a = 0](./textos/Resta_consigo_mismo.md) (En [Lean4](./src/Resta_consigo_mismo.lean)).
-   [En los anillos, 1 + 1 = 2](./textos/Uno_mas_uno_es_dos.md) (En [Lean4](./src/Uno_mas_uno_es_dos.lean)).
-   [Si R es un anillo y a ∈ R, entonces 2a = a+a](./textos/Producto_por_dos.md) (En [Lean4](./src/Producto_por_dos.lean)).


## Propiedades de orden en los números reales

-   [En ℝ, si a ≤ b, b < c, c ≤ d y d < e, entonces a < e](./textos/Cadena_de_desigualdades.md) (En [Lean4](./src/Cadena_de_desigualdades.lean)).
-   [En ℝ, si 2a ≤ 3b, 1 ≤ a y d = 2, entonces d + a ≤ 5b](./textos/Inecuaciones.md) (En [Lean4](./src/Inecuaciones.lean)).
-   [En ℝ, si 1 ≤ a y b ≤ d, entonces 2 + a + eᵇ ≤ 3a + eᵈ](./textos/Inecuaciones_con_exponenciales.md) (En [Lean4](./src/Inecuaciones_con_exponenciales.lean)).
-   [En ℝ, si a ≤ b y c < d, entonces a + eᶜ + f ≤ b + eᵈ + f](./textos/Inecuaciones_con_exponenciales_2.md) (En [Lean4](./src/Inecuaciones_con_exponenciales_2.lean)).
-   [En ℝ, si d ≤ f, entonces c + e<sup>(a + d)</sup> ≤ c + e<sup>(a + f)</sup>](./textos/Inecuaciones_con_exponenciales_3.md) (En [Lean4](./src/Inecuaciones_con_exponenciales_3.lean)).
-   [En ℝ, si a ≤ b, entonces log(1+e<sup>a</sup>) ≤ log(1+e<sup>b</sup>)](./textos/Desigualdad_logaritmica.md) (En [Lean4](./src/Desigualdad_logaritmica.lean)).
-   [En ℝ, si a ≤ b, entonces c - e<sup>b</sup> ≤ c - e<sup>a</sup>](./textos/Inecuaciones_con_exponenciales_4.md) (En [Lean4](./src/Inecuaciones_con_exponenciales_4.lean)).
-   [En ℝ, 2ab ≤ a² + b²](./textos/Doble_me_suma_cuadrados.md) (En [Lean4](./src/Doble_me_suma_cuadrados.lean)).
-   [En ℝ, |ab| ≤ (a²+b²)/2](./textos/Ejercicio_desigualdades_absolutas.md) (En [Lean4](./src/Ejercicio_desigualdades_absolutas.lean)).
-   [En ℝ, min(a,b) = min(b,a)](./textos/Conmutatividad_del_minimo.md) (En [Lean4](./src/Conmutatividad_del_minimo.lean)).
-   [En ℝ, max(a,b) = max(b,a)](./textos/Conmutatividad_del_maximo.md) (En [Lean4](./src/Conmutatividad_del_maximo.lean)).
-   [En ℝ, min(min(a,b),c) = min(a,min(b,c))](./textos/Asociatividad_del_minimo.md) (En [Lean4](./src/Asociatividad_del_minimo.lean)).
-   [En ℝ, min(a,b)+c = min(a+c,b+c)](./textos/Minimo_de_suma.md) (En [Lean4](./src/Minimo_de_suma.lean)).
-   [En ℝ, |a| - |b| ≤ |a - b|](./textos/abs_sub.md) (En [Lean4](./src/abs_sub.lean)).
-   [En ℝ, {0 < ε, ε ≤ 1, |x| < ε, |y| < ε} ⊢ |xy| < ε](./textos/Acotacion_del_producto.md) (En [Lean4](./src/Acotacion_del_producto.lean)).
-   [En ℝ, a < b → ¬(b < a)](./textos/Asimetria_de_menor.md) (En [Lean4](./src/Asimetria_de_menor.lean)).
-   [Hay algún número real entre 2 y 3](./textos/Existencia_de_valor_intermedio.md) (En [Lean4](./src/Existencia_de_valor_intermedio.lean)).
-   [Si (∀ε > 0)(x ≤ ε), entonces x ≤ 0](./textos/Condicion_para_no_positivo.md) (En [Lean4](./src/Condicion_para_no_positivo.lean)).
-   [Si 0 < 0, entonces a > 37 para cualquier número a](./textos/Principio_de_explosion.md) (En [Lean4](./src/Principio_de_explosion.lean)).
-   [{x ≤ y, y ≰ x} ⊢ x ≤ y ∧ x ≠ y](./textos/Introduccion_de_la_conjuncion.md) (En [Lean4](./src/Introduccion_de_la_conjuncion.lean)).
-   [x ≤ y ∧ x ≠ y ⊢ y ≰ x](file:///home/jalonso/alonso/estudio/Calculemus2/textos/Eliminacion_de_la_conjuncion.md) (En [Lean4](file:///home/jalonso/alonso/estudio/Calculemus2/src/Eliminacion_de_la_conjuncion.lean)).
-   [(∃x ∈ ℝ)(2 < x < 3)​](./textos/Entre_2_y_3.md) (En [Lean4](./src/Entre_2_y_3.lean)).
-   [Si (∃z ∈ ℝ)(x < z < y), entonces x < y](./textos/Menor_por_intermedio.md) (En [Lean4](./src/Menor_por_intermedio.lean)).
-   [En ℝ, x ≤ y ∧ x ≠ y → x ≤ y ∧ y ≰ x](./textos/Entre_desigualdades.md) (En [Lean4](./src/Entre_desigualdades.lean)).
-   [En ℝ, si x ≤ y, entonces y ≰ x ↔ x ≠ y](./textos/CNS_de_distintos.md) (En [Lean4](./src/CNS_de_distintos.lean)).
-   [Si |x + 3| < 5, entonces -8 < x < 2](./textos/Acotacion_del_valor_absoluto.md) (En [Lean4](./src/Acotacion_del_valor_absoluto.lean)).
-   [En ℝ, y > x² ⊢ y > 0 ∨ y < -1](./textos/Introduccion_de_la_disyuncion_1.md) (En [Lean4](./src/Introduccion_de_la_disyuncion_1.lean)).
-   [En ℝ, -y > x² + 1 ⊢ y > 0 ∨ y < -1](./textos/Introduccion_de_la_disyuncion_2.md) (En [Lean4](./src/Introduccion_de_la_disyuncion_2.lean)).
-   [En ℝ, si x < |y|, entonces x < y ó x < -y](./textos/Eliminacion_de_la_disyuncion.md) (En [Lean4](./src/Eliminacion_de_la_disyuncion.lean)).
-   [En ℝ, x ≤ |x|](./textos/Cota_inf_de_abs.md) (En [Lean4](./src/Cota_inf_de_abs.lean)).
-   [En ℝ, -x ≤ |x|](./textos/Cota_inf2_de_abs.md) (En [Lean4](./src/Cota_inf2_de_abs.lean)).
-   [En ℝ, |x + y| ≤ |x| + |y|](./textos/Desigualdad_triangular_para_valor_absoluto.md) (En [Lean4](./src/Desigualdad_triangular_para_valor_absoluto.lean)).
-   [En ℝ, si x ≠ 0 entonces x < 0 ó x > 0](./textos/Eliminacion_de_la_disyuncion_con_rcases.md) (En [Lean4](./src/Eliminacion_de_la_disyuncion_con_rcases.lean)).
-   [Si (∃ x, y ∈ ℝ)(z = x² + y² ∨ z = x² + y² + 1), entonces z ≥ 0](./textos/Desigualdad_con_rcases.md) (En [Lean4](./src/Desigualdad_con_rcases.lean)).
-   [En ℝ, si 1 < a, entonces a < aa](./textos/Demostracion_por_conversion.md) (En [Lean4](./src/Demostracion_por_conversion.lean)).
-   [Si x, y ∈ ℝ tales que (∀ z)[y < z → x ≤ z], entonces x ≤ y](./textos/Propiedad_de_la_densidad_de_los_reales.md) (En [Lean](./src/Propiedad_de_la_densidad_de_los_reales.lean) y en [Isabelle](./thy/Propiedad_de_la_densidad_de_los_reales.thy)).


## Divisibilidad

-   [Si x, y, z ∈ ℕ, entonces x divide a yxz](./textos/Divisibilidad_de_producto.md) (En [Lean4](./src/Divisibilidad_de_producto.lean)).
-   [Si x divide a w, también divide a y(xz)+x²+w²](./textos/Ejercicio_de_divisibilidad.md) (En [Lean4](./src/Ejercicio_de_divisibilidad.lean)).
-   [Transitividad de la divisibilidad](./textos/Transitividad_de_la_divisibilidad.md) (En [Lean4](./src/Transitividad_de_la_divisibilidad.lean)).
-   [Si a divide a b y a c, entonces divide a b+c](./textos/Suma_divisible.md) (En [Lean4](./src/Suma_divisible.lean)).
-   [Conmutatividad del máximo común divisor](./textos/Conmutatividad_del_gcd.md) (En [Lean4](./src/Conmutatividad_del_gcd.lean)).
-   [Si (m ∣ n ∧ m ≠ n), entonces (m ∣ n ∧ ¬(n ∣ m))](./textos/Uso_de_conjuncion.md) (En [Lean4](./src/Uso_de_conjuncion.lean)).
-   [Existen números primos m y n tales que 4 < m < n < 10](./textos/Primos_intermedios.md) (En [Lean4](./src/Primos_intermedios.lean)).
-   [3 divide al máximo común divisor de 6 y 15](./textos/Divisor_del_mcd.md) (En [Lean4](./src/Divisor_del_mcd.lean)).
-   [Si m divide a n o a k, entonces m divide a nk](./textos/CS_de_divisibilidad_del_producto.md) (En [Lean4](./src/CS_de_divisibilidad_del_producto.lean)).
-   [Existen infinitos números primos](./textos/Infinitud_de_primos.md) (En [Lean4](./src/Infinitud_de_primos.lean)).
-   [Si n² es par, entonces n es par](./textos/Par_si_cuadrado_par.md) (En [Lean4](./src/Par_si_cuadrado_par.lean)).
-   [La raíz cuadrada de 2 es irracional](./textos/Irracionalidad_de_la_raiz_cuadrada_de_2.md) (En [Lean](./src/Irracionalidad_de_la_raiz_cuadrada_de_2.lean)).
-   [Un número es par si y solo si lo es su cuadrado](./textos/Un_numero_es_par_syss_lo_es_su_cuadrado.md) (En [Lean](./src/Un_numero_es_par_syss_lo_es_su_cuadrado.lean) y en [Isabelle](./thy/Un_numero_es_par_syss_lo_es_su_cuadrado.thy)).


## Retículos

-   [En los retículos, x ⊓ y = y ⊓ x](./textos/Conmutatividad_del_infimo.md) (En [Lean4](./src/Conmutatividad_del_infimo.lean)).
-   [En los retículos, x ⊔ y = y ⊔ x](./textos/Conmutatividad_del_supremo.md) (En [Lean4](./src/Conmutatividad_del_supremo.lean)).
-   [En los retículos, (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)](./textos/Asociatividad_del_infimo.md) (En [Lean4](./src/Asociatividad_del_infimo.lean)).
-   [En los retículos, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)](./textos/Asociatividad_del_supremo.md) (En [Lean4](./src/Asociatividad_del_supremo.lean)).
-   [En los retículos, x ⊓ (x ⊔ y) = x](./textos/Leyes_de_absorcion_1.md) (En [Lean4](./src/Leyes_de_absorcion_1.lean)).
-   [En los retículos, x ⊔ (x ⊓ y) = x](./textos/Leyes_de_absorcion_2.md) (En [Lean4](./src/Leyes_de_absorcion_2.lean)).
-   [En los retículos, una distributiva del ínfimo implica la otra](./textos/propiedad_distributiva_1.md) (En [Lean4](./src/Propiedad_distributiva_1.lean)).
-   [En los retículos, una distributiva del supremos implica la otra](./textos/Propiedad_distributiva_2.md) (En [Lean4](./src/Propiedad_distributiva_2.lean)).


## Relaciones de orden

-   [En los órdenes parciales, a < b ↔ a ≤ b ∧ a ≠ b](./textos/Caracterizacion_de_menor_en_ordenes_parciales.md) (En [Lean4](./src/Caracterizacion_de_menor_en_ordenes_parciales.lean)).
-   [Si ≤ es un preorden, entonces < es irreflexiva](./textos/Preorden_es_irreflexivo.md) (En [Lean4](./src/Preorden_es_irreflexivo.lean)).
-   [Si ≤ es un preorden, entonces < es transitiva](./textos/Preorden_transitiva.md) (En [Lean4](./src/Preorden_transitiva.lean)).


## Relaciones de equivalencia

-   [La congruencia módulo 2 es una relación de equivalencia](./textos/La_congruencia_modulo_2_es_una_relacion_de_equivalencia.md) (En [Lean](./src/La_congruencia_modulo_2_es_una_relacion_de_equivalencia.lean) y en [Isabelle](./thy/La_congruencia_modulo_2_es_una_relacion_de_equivalencia.thy)).


## Anillos ordenados

-   [En los anillos ordenados, a ≤ b → 0 ≤ b - a](./textos/Ejercicio_sobre_anillos_ordenados.md) (En [Lean4](./src/Ejercicio_sobre_anillos_ordenados_1.lean)).
-   [En los anillos ordenados, 0 ≤ b - a → a ≤ b](./textos/Ejercicio_sobre_anillos_ordenados_2.md) (En [Lean4](./src/Ejercicio_sobre_anillos_ordenados_2.lean)).
-   [En los anillos ordenados, {a ≤ b, 0 ≤ c} ⊢ ac ≤ bc](./textos/Ejercicio_sobre_anillos_ordenados_3.md) (En [Lean4](./src/Ejercicio_sobre_anillos_ordenados_3.lean)).


## Espacios métricos

-   [En los espacios métricos, dist(x,y) ≥ 0](./textos/Ejercicio_en_espacios_metricos.md) (En [Lean4](./src/Ejercicio_en_espacios_metricos.lean)).


## Funciones reales

-   [La suma de una cota superior de f y una cota superior de g es una cota superior de f+g](./textos/Suma_de_cotas_superiores.md) (En [Lean4](./src/Suma_de_cotas_superiores.lean)).
-   [La suma de una cota inferior de f y una cota inferior de g es una cota inferior de f+g](./textos/Suma_de_cotas_inferiores.md) (En [Lean4](./src/Suma_de_cotas_inferiores.lean)).
-   [El producto de funciones no negativas es no negativo](./textos/Producto_de_funciones_no_negativas.md) (En [Lean4](./src/Producto_de_funciones_no_negativas.lean)).
-   [Si a es una cota superior no negativa de f y b es es una cota superior de la función no negativa g, entonces ab es una cota superior de fg](./textos/Cota_superior_del_producto.md) (En [Lean4](./src/Cota_superior_del_producto.lean)).
-   [La suma de dos funciones acotadas superiormente también lo está](./textos/Suma_de_funciones_acotadas_superiormente.md) (En [Lean4](./src/Suma_de_funciones_acotadas_superiormente.lean)).
-   [La suma de dos funciones acotadas inferiormente también lo está](./textos/Suma_de_funciones_acotadas_inferiormente.md) (En [Lean4](./src/Suma_de_funciones_acotadas_inferiormente.lean)).
-   [Si a es una cota superior de f y c ≥ 0, entonces ca es una cota superior de cf](./textos/Cota_superior_de_producto_por_escalar.md) (En [Lean4](./src/Cota_superior_de_producto_por_escalar.lean)).
-   [Si c ≥ 0 y f está acotada superiormente, entonces c·f también lo está](./textos/Producto_por_escalar_acotado_superiormente.md) (En [Lean4](./src/Producto_por_escalar_acotado_superiormente.lean)).
-   [Si para cada a existe un x tal que f(x) > a, entonces f no tiene cota superior](./textos/Funcion_no_acotada_superiormente.md) (En [Lean4](./src/Funcion_no_acotada_superiormente.lean)).
-   [Si para cada a existe un x tal que f(x) < a, entonces f no tiene cota inferior](./textos/Funcion_no_acotada_inferiormente.md) (En [Lean4](./src/Funcion_no_acotada_inferiormente.lean)).
-   [La función identidad no está acotada superiormente](./textos/La_identidad_no_esta_acotada_superiormente.md) (En [Lean4](./src/La_identidad_no_esta_acotada_superiormente.lean)).
-   [Si f no está acotada superiormente, entonces (∀a)(∃x)(f(x) > a)​](./textos/CN_no_acotada_superiormente.md) (En [Lean4](./src/CN_no_acotada_superiormente.lean)).
-   [Si ¬(∀a)(∃x)(f(x) > a)​, entonces f está acotada superiormente](./textos/CS_de_acotada_superiormente.md) (En [Lean4](./src/CS_de_acotada_superiormente.lean)).
-   [Suma de funciones monótonas](./textos/Suma_de_funciones_monotonas.md) (En [Lean4](./src/Suma_de_funciones_monotonas.lean)).
-   [Si c es no negativo y f es monótona, entonces cf es monótona.](./textos/Producto_de_un_positivo_por_una_funcion_monotona.md) (En [Lean4](./src/Producto_de_un_positivo_por_una_funcion_monotona.lean)).
-   [La composición de dos funciones monótonas es monótona](./textos/Composicion_de_funciones_monotonas.md) (En [Lean4](./src/Composicion_de_funciones_monotonas.lean)).
-   [Si f es monótona y f(a) < f(b), entonces a < b](./textos/CN_de_monotona.md) (En [Lean4](./src/CN_de_monotona.lean)).
-   [Si a, b ∈ ℝ tales que a ≤ b y f(b) < f(a), entonces f no es monótona](./textos/CS_de_no_monotona.md) (En [Lean4](./src/CS_de_no_monotona.lean)).
-   [No para toda f : ℝ → ℝ monótona, (∀a,b)(f(a) ≤ f(b) → a ≤ b)​](file:///home/jalonso/alonso/estudio/Calculemus2/textos/Propiedad_de_monotona.md) (En [Lean4](file:///home/jalonso/alonso/estudio/Calculemus2/src/Propiedad_de_monotona.lean)).
-   [Si f no es monótona, entonces ∃x∃y(x ≤ y ∧ f(y) < f(x))​](./textos/CN_de_no_monotona.md) (En [Lean4](./src/CN_de_no_monotona.lean)).
-   [f: ℝ → ℝ no es monótona syss (∃x,y)(x ≤ y ∧ f(x) > f(y))​](./textos/CNS-de_no_monotona.md) (En [Lean4](./src/CNS_de_no_monotona.lean)).
-   [La función x ↦ -x no es monótona creciente](./textos/La_opuesta_es_no_monotona.md) (En [Lean4](./src/La_opuesta_es_no_monotona.lean)).
-   [La suma de dos funciones pares es par](./textos/Suma_funciones_pares.md) (En [Lean4](./src/Suma_funciones_pares.lean)).
-   [El producto de dos funciones impares es par](./textos/Producto_de_funciones_impares.md) (En [Lean4](./src/Producto_de_funciones_impares.lean)).
-   [El producto de una función par por una impar es impar](./textos/Producto_funcion_par_e_impar.md) (En [Lean4](./src/Producto_funcion_par_e_impar.lean)).
-   [Si f es par y g es impar, entonces (f ∘ g) es par](./textos/Composicion_de_par_e_impar.md) (En [Lean4](./src/Composicion_de_par_e_impar.lean)).
-   [Las funciones f(x,y) = (x + y)² y g(x,y) = x² + 2xy + y² son iguales](./textos/Demostracion_por_extensionalidad.md) (En [Lean4](./src/Demostracion_por_extensionalidad.lean)).
-   [La composición de una función creciente y una decreciente es decreciente](./textos/La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.md) (En [Lean](./src/La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean) y en [Isabelle](./thy/La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.thy)).
-   [Si una función es creciente e involutiva, entonces es la identidad](./textos/Una_funcion_creciente_e_involutiva_es_la_identidad.md) (En [Lean](./src/Una_funcion_creciente_e_involutiva_es_la_identidad.lean) y en [Isabelle](./thy/Una_funcion_creciente_e_involutiva_es_la_identidad.thy)).
-   [Si \`f(x) ≤ f(y) → x ≤ y\`, entonces f es inyectiva](./textos/Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.md) (En [Lean](./src/Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.lean) y en [Isabelle](./thy/Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.thy)).
-   [Las funciones con inversa por la izquierda son inyectivas](./textos/Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.md) (En [Lean](./src/Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.lean) y en [Isabelle](./thy/Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.thy)).
-   [Si g ∘ f es inyectiva, entonces f es inyectiva](./textos/Inyectiva_si_lo_es_la_composicion.md) (En [Lean4](./src/Inyectiva_si_lo_es_la_composicion.lean) y en [Isabelle](./thy/Inyectiva_si_lo_es_la_composicion.thy)).


## Teoría de conjuntos

-   [Para cualquier conjunto s, s ⊆ s](./textos/Propiedad_reflexiva_del_subconjunto.md) (En [Lean4](./src/Propiedad_reflexiva_del_subconjunto.lean)).
-   [Si r ⊆ s y s ⊆ t, entonces r ⊆ t](./textos/Propiedad_transitiva_del_subconjunto.md) (En [Lean4](./src/Propiedad_transitiva_del_subconjunto.lean)).
-   [Si s ⊆ t, entonces s ∩ u ⊆ t ∩ u](./textos/Propiedad_de_monotonia_de_la_interseccion.md) (En [Lean](./src/Propiedad_de_monotonia_de_la_interseccion.lean) y en [Isabelle](./thy//Propiedad_de_monotonia_de_la_interseccion.thy)).
-   [s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)](./textos/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.md) (En [Lean](./src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.lean) y en [Isabelle](./thy/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union.thy)).
-   [(s \\ t) \\ u ⊆ s \\ (t ∪ u)](./textos/Diferencia_de_diferencia_de_conjuntos.md) (En [Lean](./src/Diferencia_de_diferencia_de_conjuntos.lean) y en [Isabelle](./thy/Diferencia_de_diferencia_de_conjuntos.thy)).
-   [(s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)](./textos/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.md) (En [Lean](./src/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.lean) y en [Isabelle](./thy/Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.thy)).
-   [s \\ (t ∪ u) ⊆ (s \\ t) \\ u](./textos/Diferencia_de_diferencia_de_conjuntos_2.md) (En [Lean](./src/Diferencia_de_diferencia_de_conjuntos_2.lean) y en [Isabelle](./thy/Diferencia_de_diferencia_de_conjuntos.thy)).
-   [s ∩ t = t ∩ s](./textos/Conmutatividad_de_la_interseccion.md) (En [Lean](./src/Conmutatividad_de_la_interseccion.lean) y en [Isabelle](./thy/Conmutatividad_de_la_interseccion.thy)).
-   [s ∩ (s ∪ t) = s](./textos/Interseccion_con_su_union.md) (En [Lean](./src/Interseccion_con_su_union.lean) y en [Isabelle](./thy/Interseccion_con_su_union.thy)).
-   [s ∪ (s ∩ t) = s](./textos/Union_con_su_interseccion.md) (En [Lean](./src/Union_con_su_interseccion.lean) y en [Isabelle](./thy/Union_con_su_interseccion.thy)).
-   [(s \\ t) ∪ t = s ∪ t](./textos/Union_con_su_diferencia.md) (En [Lean](./src/Union_con_su_diferencia.lean) y en [Isabelle](./thy/Union_con_su_diferencia.thy)).
-   [(s \\ t) ∪ (t \\ s) = (s ∪ t) \\ (s ∩ t)](./textos/Diferencia_de_union_e_interseccion.md) (En [Lean](./src/Diferencia_de_union_e_interseccion.lean) y en [Isabelle](./thy/Diferencia_de_union_e_interseccion.thy)).
-   [pares ∪ impares = naturales](./textos/Union_de_pares_e_impares.md) (En [Lean](./src/Union_de_pares_e_impares.lean) y en [Isabelle](./thy/Union_de_pares_e_impares.thy)).
-   [Los primos mayores que 2 son impares](./textos/Interseccion_de_los_primos_y_los_mayores_que_dos.md) (En [Lean](./src/Interseccion_de_los_primos_y_los_mayores_que_dos.lean) y en [Isabelle](./thy/Interseccion_de_los_primos_y_los_mayores_que_dos.thy)).
-   [s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)](./textos/Distributiva_de_la_interseccion_respecto_de_la_union_general.md) (En [Lean](./src/Distributiva_de_la_interseccion_respecto_de_la_union_general.lean) y en [Isabelle](./thy/Distributiva_de_la_interseccion_respecto_de_la_union_general.thy)).
-   [(⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)](./textos/Interseccion_de_intersecciones.md) (En [Lean](./src/Interseccion_de_intersecciones.lean) y en [Isabelle](./thy/Interseccion_de_intersecciones.thy)).
-   [s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)](./textos/Union_con_interseccion_general.md) (En [Lean](./src/Union_con_interseccion_general.lean) y en [Isabelle](./thy/Union_con_interseccion_general.thy)).
-   [f⁻¹[u ∩ v] = f⁻¹[u] ∩ f⁻¹[v]​](./textos/Imagen_inversa_de_la_interseccion.md) (En [Lean](./src/Imagen_inversa_de_la_interseccion.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_interseccion.thy)).
-   [f[s ∪ t] = f[s] ∪ f[t]​](./textos/Imagen_de_la_union.md) (En [Lean](./src/Imagen_de_la_union.lean) y en [Isabelle](./thy/Imagen_de_la_union.thy)).
-   [s ⊆ f⁻¹[f[s]​]​](./textos/Imagen_inversa_de_la_imagen.md) (En [Lean](./src/Imagen_inversa_de_la_imagen.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_imagen.thy)).
-   [f[s] ⊆ u ↔ s ⊆ f⁻¹[u]​](./textos/Subconjunto_de_la_imagen_inversa.md) (En [Lean](./src/Subconjunto_de_la_imagen_inversa.lean) y en [Isabelle](./thy/Subconjunto_de_la_imagen_inversa.thy)).
-   [Si a es una cota superior de s y a ≤ b, entonces b es una cota superior de s](./textos/Cotas_superiores_de_conjuntos.md) (En [Lean4](./src/Cotas_superiores_de_conjuntos.lean)).
-   [La función (x ↦ x + c) es inyectiva](./textos/Suma_constante_es_inyectiva.md) (En [Lean4](./src/Suma_constante_es_inyectiva.lean)).
-   [Si c ≠ 0, entonces la función (x ↦ cx) es inyectiva](./textos/Producto_constante_no_nula_es_inyectiva.md) (En [Lean4](./src/Producto_constante_no_nula_es_inyectiva.lean)).
-   [La composición de funciones inyectivas es inyectiva](./textos/Composicion_de_funciones_inyectivas.md) (En [Lean4](./src/Composicion_de_funciones_inyectivas.lean)).
-   [La función (x ↦ x + c) es suprayectiva](./textos/Suma_constante_es_suprayectiva.md) (En [Lean4](./src/Suma_constante_es_suprayectiva.lean)).
-   [Si c ≠ 0, entonces la función (x ↦ cx) es suprayectiva](./textos/Producto_por_no_nula_es_suprayectiva.md) (En [Lean4](./src/Producto_por_no_nula_es_suprayectiva.lean)).
-   [Si c ≠ 0, entonces la función (x ↦ cx + d) es suprayectiva](./textos/Producto_por_no_nula_y_suma_es_suprayectiva.md) (En [Lean4](./src/Producto_por_no_nula_y_suma_es_suprayectiva.lean)).
-   [Si f: ℝ → ℝ es suprayectiva, entonces ∃x ∈ ℝ tal que f(x)² = 9](./textos/Propiedad_de_suprayectivas.md) (En [Lean4](./src/Propiedad_de_suprayectivas.lean)).
-   [La composición de funciones suprayectivas es suprayectiva](./textos/Composicion_de_suprayectivas.md) (En [Lean4](./src/Composicion_de_suprayectivas.lean)).
-   [Si f es inyectiva, entonces f⁻¹[f[s]​] ⊆ s](./textos/Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.md) (En [Lean](./src/Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.thy)).
-   [f[f⁻¹[u]​] ⊆ u](./textos/Imagen_de_la_imagen_inversa.md) (En [Lean](./src/Imagen_de_la_imagen_inversa.lean) y en [Isabelle](./thy/Imagen_de_la_imagen_inversa.thy)).
-   [Si f es suprayectiva, entonces u ⊆ f[f⁻¹[u]​]​](./textos/Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.md) (En [Lean](./src/Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.lean) y en [Isabelle](./thy/Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.thy)).
-   [Si s ⊆ t, entonces f[s] ⊆ f[t]​](./textos/Monotonia_de_la_imagen_de_conjuntos.md) (En [Lean](./src/Monotonia_de_la_imagen_de_conjuntos.lean) y en [Isabelle](./thy/Monotonia_de_la_imagen_de_conjuntos.thy)).
-   [Si u ⊆ v, entonces f⁻¹[u] ⊆ f⁻¹[v]​](./textos/Monotonia_de_la_imagen_inversa.md) (En [Lean](./src/Monotonia_de_la_imagen_inversa.lean) y en [Isabelle](./thy/Monotonia_de_la_imagen_inversa.thy)).
-   [f⁻¹[A ∪ B] = f⁻¹[A] ∪ f⁻¹[B]​](./textos/Imagen_inversa_de_la_union.md) (En [Lean](./src/Imagen_inversa_de_la_union.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_union.thy)).
-   [f[s ∩ t] ⊆ f[s] ∩ f[t]​](./textos/Imagen_de_la_interseccion.md) (En [Lean](./src/Imagen_de_la_interseccion.lean) y en [Isabelle](./thy/Imagen_de_la_interseccion.thy)).
-   [Si f es inyectiva, entonces f[s] ∩ f[t] ⊆ f[s ∩ t]​](./textos/Imagen_de_la_interseccion_de_aplicaciones_inyectivas.md) (En [Lean](./src/Imagen_de_la_interseccion_de_aplicaciones_inyectivas.lean) y en [Isabelle](./thy/Imagen_de_la_interseccion_de_aplicaciones_inyectivas.thy)).
-   [f[s] \\ f[t] ⊆ f[s \\ t]​](./textos/Imagen_de_la_diferencia_de_conjuntos.md) (En [Lean](./src/Imagen_de_la_diferencia_de_conjuntos.lean) y en [Isabelle](./thy/Imagen_de_la_diferencia_de_conjuntos.thy)).
-   [f[s] ∩ v = f[s ∩ f⁻¹[v]​]​](./textos/Interseccion_con_la_imagen.md) (En [Lean](./src/Interseccion_con_la_imagen.lean) y en [Isabelle](./thy/Interseccion_con_la_imagen.thy)).
-   [Unión con la imagen](./textos/Union_con_la_imagen.md) (En [Lean](./src/Union_con_la_imagen.lean) y en [Isabelle](./thy/Union_con_la_imagen.thy)).
-   [Intersección con la imagen inversa](./textos/Interseccion_con_la_imagen_inversa.md) (En [Lean](./src/Interseccion_con_la_imagen_inversa.lean) y en [Isabelle](./thy/Interseccion_con_la_imagen_inversa.thy)).
-   [Unión con la imagen inversa](./textos/Union_con_la_imagen_inversa.md) (En [Lean](./src/Union_con_la_imagen_inversa.lean) y en [Isabelle](./thy/Union_con_la_imagen_inversa.thy)).
-   [Imagen de la unión general](./textos/Imagen_de_la_union_general.md) (En [Lean](./src/Imagen_de_la_union_general.lean) y en [Isabelle](./thy/Imagen_de_la_union_general.thy)).
-   [Imagen de la intersección general](./textos/Imagen_de_la_interseccion_general.md) (En [Lean](./src/Imagen_de_la_interseccion_general.lean) y en [Isabelle](./thy/Imagen_de_la_interseccion_general.thy)).
-   [Imagen de la intersección general mediante aplicaciones inyectivas](./textos/Imagen_de_la_interseccion_general_mediante_inyectiva.md) (En [Lean](./src/Imagen_de_la_interseccion_general_mediante_inyectiva.lean) y en [Isabelle](./thy/Imagen_de_la_interseccion_general_mediante_inyectiva.thy)).
-   [Imagen inversa de la unión general](./textos/Imagen_inversa_de_la_union_general.md) (En [Lean](./src/Imagen_inversa_de_la_union_general.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_union_general.thy)).
-   [Imagen inversa de la intersección general](./textos/Imagen_inversa_de_la_interseccion_general.md) (En [Lean](./src/Imagen_inversa_de_la_interseccion_general.lean) y en [Isabelle](./thy/Imagen_inversa_de_la_interseccion_general.thy)).
-   [Teorema de Cantor](./textos/Teorema_de_Cantor.md) (En [Lean](./src/Teorema_de_Cantor.lean) y en [Isabelle](./thy/Teorema_de_Cantor.thy)).
-   [Si g ∘ f es suprayectiva, entonces g es suprayectiva](./textos/Suprayectiva_si_lo_es_la_composicion.md) (En [Lean4](./src/Suprayectiva_si_lo_es_la_composicion.lean) y en [Isabelle](./thy/Suprayectiva_si_lo_es_la_composicion.thy)).
-   [Las funciones inyectivas tienen inversa por la izquierda](./textos/Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.md) (En [Lean](./src/Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.lean) y en [Isabelle](./thy/Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.thy)).
-   [Las funciones con inversa por la derecha son suprayectivas](./textos/Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.md) (En [Lean](./src/Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.lean) y en [Isabelle](./thy/Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.thy)).
-   [Las funciones suprayectivas tienen inversa por la derecha](./textos/Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.md) (En [Lean](./src/Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.lean) y en [Isabelle](./thy/Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.thy)).
-   [Las funciones con inversa son biyectivas](./textos/Las_funciones_con_inversa_son_biyectivas.md) (En [Lean](./src/Las_funciones_con_inversa_son_biyectivas.lean) y en [Isabelle](./thy/Las_funciones_con_inversa_son_biyectivas.thy)).
-   [Las funciones biyectivas tienen inversa](./textos/Las_funciones_biyectivas_tienen_inversa.md) (En [Lean](./src/Las_funciones_biyectivas_tienen_inversa.lean) y en [Isabelle](./thy/Las_funciones_biyectivas_tienen_inversa.thy)).
-   [La equipotencia es una relación reflexiva](./textos/La_equipotencia_es_una_relacion_reflexiva.md) (En [Lean](./src/La_equipotencia_es_una_relacion_reflexiva.lean) y en [Isabelle](./thy/La_equipotencia_es_una_relacion_reflexiva.thy)).
-   [La inversa de una función es biyectiva](./textos/La_inversa_de_una_funcion_biyectiva_es_biyectiva.md) (En [Lean](./src/La_inversa_de_una_funcion_biyectiva_es_biyectiva.lean) y en [Isabelle](./thy/La_inversa_de_una_funcion_biyectiva_es_biyectiva.thy)).
-   [La equipotencia es una relación simétrica](./textos/La_equipotencia_es_una_relacion_simetrica.md) (En [Lean](./src/La_equipotencia_es_una_relacion_simetrica.lean) y en [Isabelle](./thy/La_equipotencia_es_una_relacion_simetrica.thy)).
-   [La composición de funciones biyectivas es biyectiva](./textos/La_composicion_de_funciones_biyectivas_es_biyectiva.md) (En [Lean](./src/La_composicion_de_funciones_biyectivas_es_biyectiva.lean) y en [Isabelle](./thy/La_composicion_de_funciones_biyectivas_es_biyectiva.thy)).


## Lógica

-   [Si ¬(∃x)P(x), entonces (∀x)¬P(x)](./textos/Para_todo_no_de_no_existe.md) (En [Lean4](./src/Para_todo_no_de_no_existe.lean)).
-   [Si (∀x)¬P(x), entonces ¬(∃x)P(x)](./textos/No_existe_de_para_todo_no.md) (En [Lean4](./src/No_existe_de_para_todo_no.lean)).
-   [Si ¬(∀x)P(x), entonces (∃x)¬P(x)](./textos/Existe_no_de_no_para_todo.md) (En [Lean4](./src/Existe_no_de_no_para_todo.lean)).
-   [Si (∃x)¬P(x), entonces ¬(∀x)P(x)](./textos/No_para_todo_de_existe_no.md) (En [Lean4](./src/No_para_todo_de_existe_no.lean)).
-   [¬¬P → P](./textos/Eliminacion_doble_negacion.md) (En [Lean4](./src/Eliminacion_doble_negacion.lean)).
-   [P → ¬¬P](./textos/Introduccion_doble_negacion.md) (En [Lean4](./src/Introduccion_doble_negacion.lean)).
-   [(P → Q) ↔ ¬P ∨ Q](./textos/Implicacion_mediante_disyuncion_y_negacion.md) (En [Lean4](./src/Implicacion_mediante_disyuncion_y_negacion.lean)).
-   [La paradoja del barbero](./textos/La_paradoja_del_barbero.md) (En [Lean](./src/La_paradoja_del_barbero.lean) y en [Isabelle](./thy/La_paradoja_del_barbero.thy)).


## Límites de sucesiones

-   [La sucesión constante sₙ = c converge a c](./textos/Convergencia_de_la_sucesion_constante.md) (en [Lean4](./src/Convergencia_de_la_sucesion_constante.lean) y en [Isabelle](./thy/Limite_de_sucesiones_constantes.thy)).
-   [Si la sucesión s converge a b y la t a c, entonces s+t converge a b+c](./textos/Convergencia_de_la_suma.md) (En [Lean4](./src/Convergencia_de_la_suma.lean) y en [Isabelle](./thy/Limite_de_la_suma_de_sucesiones_convergentes.thy)).
-   [Unicidad del límite de las sucesiones convergentes](./textos/Unicidad_del_limite_de_las_sucesiones_convergentes.md) (En [Lean4](./src/Unicidad_del_limite_de_las_sucesiones_convergentes.lean) y en [Isabelle](./thy/Unicidad_del_limite_de_las_sucesiones_convergentes.thy)).
-   [Si el límite de la sucesión uₙ es a y c ∈ ℝ, entonces el límite de uₙ+c es a+c](./textos/Limite_cuando_se_suma_una_constante.md) (En [Lean](./src/Limite_cuando_se_suma_una_constante.lean) y en [Isabelle](./thy/Limite_cuando_se_suma_una_constante.thy)).
-   [Si el límite de la sucesión u(n) es a y c ∈ ℝ, entonces el límite de cu(n) es ca](file:///home/jalonso/alonso/estudio/Calculemus2/textos/Limite_multiplicado_por_una_constante.md) (En [Lean](./src/Limite_multiplicado_por_una_constante.lean) y en [Isabelle](./thy/Limite_multiplicado_por_una_constante.thy)).
-   [El límite de u es a syss el de u-a es 0](./textos/El_limite_de_u_es_a_syss_el_de_u-a_es_0.md) (En [Lean](./src/El_limite_de_u_es_a_syss_el_de_u-a_es_0.lean) y en [Isabelle](./thy/El_limite_de_u_es_a_syss_el_de_u-a_es_0.thy)).
-   [Si uₙ y vₙ convergen a 0, entonces uₙvₙ converge a 0](./textos/Producto_de_sucesiones_convergentes_a_cero.md) (En [Lean](./src/Producto_de_sucesiones_convergentes_a_cero.lean) y en [Isabelle](./thy/Producto_de_sucesiones_convergentes_a_cero.thy)).
-   [Teorema del emparedado](file:///home/jalonso/alonso/estudio/Calculemus2/textos/Teorema_del_emparedado.md) (En [Lean](./src/Teorema_del_emparedado.lean) y en [Isabelle](./thy/Teorema_del_emparedado.thy)).
-   [Los supremos de las sucesiones crecientes son sus límites](./textos/Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.md) (En [Lean](./src/Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean) y en [Isabelle](./thy/Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.thy)).
-   [Las sucesiones convergentes están acotadas](./textos/Acotacion_de_convergentes.md) (En [Lean](./src/Acotacion_de_convergentes.lean) y en [Isabelle](./thy/Acotacion_de_convergentes.thy)).
-   [Si (∀n)[uₙ ≤ vₙ], entonces lim uₙ ≤ lim vₙ](./textos/Limite_de_sucesion_menor_que_otra_sucesion.md) (En [Lean](./src/Limite_de_sucesion_menor_que_otra_sucesion.lean) y en [Isabelle](./thy/Limite_de_sucesion_menor_que_otra_sucesion.thy)).
-   [Si uₙ está acotada y lim vₙ = 0, entonces lim (uₙ·vₙ) = 0](./textos/Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.md) (En [Lean](./src/Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.lean) y en [Isabelle](./thy/Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.thy)).
-   [Si el límite de la sucesión uₙ es a, entonces el límite de -uₙ es -a](./textos/Limite_de_la_opuesta.md) (En [Lean](./src/Limite_de_la_opuesta.lean) y en [Isabelle](./thy/Limite_de_la_opuesta.thy)).

