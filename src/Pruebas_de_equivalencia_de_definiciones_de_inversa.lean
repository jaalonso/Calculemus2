-- Pruebas_de_equivalencia_de_definiciones_de_inversa.lean
-- Pruebas de equivalencia de definiciones de inversa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, está definida la función
--    reverse : list α → list α
-- tal que (reverse xs) es la lista obtenida invirtiendo el orden de los
-- elementos de xs. Por ejemplo,
--    reverse  [3,2,5,1] = [1,5,2,3]
-- Su definición es
--    def reverse_core : list α → list α → list α
--    | []     r := r
--    | (a::l) r := reverse_core l (a::r)
--
--    def reverse : list α → list α :=
--    λ l, reverse_core l []
--
-- Una definición alternativa es
--    def inversa : list α → list α
--    | []        := []
--    | (x :: xs) := inversa xs ++ [x]
--
-- Demostrar que las dos definiciones son equivalentes; es decir,
--    reverse xs = inversa xs
-- ---------------------------------------------------------------------

import data.list.basic
open list

variable  {α : Type*}
variable  (x : α)
variables (xs ys : list α)

-- Definición y reglas de simplificación de inversa
-- ================================================

def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

@[simp]
lemma inversa_nil :
  inversa ([] : list α) = [] :=
rfl

@[simp]
lemma inversa_cons :
  inversa (x :: xs) = inversa xs ++ [x] :=
rfl

-- Reglas de simplificación de reverse_core
-- ========================================

@[simp]
lemma reverse_core_nil :
  reverse_core [] ys = ys :=
rfl

@[simp]
lemma reverse_core_cons :
  reverse_core (x :: xs) ys = reverse_core xs (x :: ys) :=
rfl

-- Lema auxiliar: reverse_core xs ys = (inversa xs) ++ ys
-- ======================================================

-- 1ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : reverse_core_nil ys
     ... = [] ++ ys                  : (nil_append ys).symm
     ... = inversa [] ++ ys          : congr_arg2 (++) inversa_nil.symm rfl, },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : reverse_core_cons a as ys
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : congr_arg2 (++) rfl singleton_append
     ... = (inversa as ++ [a]) ++ ys : (append_assoc (inversa as) [a] ys).symm
     ... = inversa (a :: as) ++ ys   : congr_arg2 (++) (inversa_cons a as).symm rfl},
end

-- 2ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : by rw reverse_core_nil
     ... = [] ++ ys                  : by rw nil_append
     ... = inversa [] ++ ys          : by rw inversa_nil },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by rw reverse_core_cons
     ... = inversa as ++ (a :: ys)   : by rw (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : by rw singleton_append
     ... = (inversa as ++ [a]) ++ ys : by rw append_assoc
     ... = inversa (a :: as) ++ ys   : by rw inversa_cons },
end

-- 3ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : rfl
     ... = [] ++ ys                  : rfl
     ... = inversa [] ++ ys          : rfl },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : rfl
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : rfl
     ... = (inversa as ++ [a]) ++ ys : by rw append_assoc
     ... = inversa (a :: as) ++ ys   : rfl },
end

-- 3ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { calc reverse_core [] ys
         = ys                        : by simp
     ... = [] ++ ys                  : by simp
     ... = inversa [] ++ ys          : by simp },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by simp
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa as ++ ([a] ++ ys) : by simp
     ... = (inversa as ++ [a]) ++ ys : by simp
     ... = inversa (a :: as) ++ ys   : by simp },
end

-- 4ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { by simp, },
  { calc reverse_core (a :: as) ys
         = reverse_core as (a :: ys) : by simp
     ... = inversa as ++ (a :: ys)   : (HI (a :: ys))
     ... = inversa (a :: as) ++ ys   : by simp },
end

-- 5ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { simp, },
  { simp [HI (a :: ys)], },
end

-- 6ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
by induction xs generalizing ys ; simp [*]

-- 7ª demostración del lema auxiliar
example :
  reverse_core xs ys = (inversa xs) ++ ys :=
begin
  induction xs with a as HI generalizing ys,
  { rw reverse_core_nil,
    rw inversa_nil,
    rw nil_append, },
  { rw reverse_core_cons,
    rw (HI (a :: ys)),
    rw inversa_cons,
    rw append_assoc,
    rw singleton_append, },
end

-- 8ª demostración  del lema auxiliar
@[simp]
lemma inversa_equiv :
  ∀ xs : list α, ∀ ys, reverse_core xs ys = (inversa xs) ++ ys
| []         := by simp
| (a :: as)  := by simp [inversa_equiv as]

-- Demostraciones del lema principal
-- =================================

-- 1ª demostración
example : reverse xs = inversa xs :=
calc reverse xs
     = reverse_core xs [] : rfl
 ... = inversa xs ++ []   : by rw inversa_equiv
 ... = inversa xs         : by rw append_nil

-- 2ª demostración
example : reverse xs = inversa xs :=
by simp [inversa_equiv, reverse]

-- 3ª demostración
example : reverse xs = inversa xs :=
by simp [reverse]
