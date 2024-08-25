-- Pruebas_de_equivalencia_de_definiciones_de_inversa.lean
-- Pruebas de equivalencia de definiciones de inversa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 19-agosto-2024
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean4, está definida la función
--    reverse : List α → List α
-- tal que (reverse xs) es la lista obtenida invirtiendo el orden de los
-- elementos de xs. Por ejemplo,
--    reverse  [3,2,5,1] = [1,5,2,3]
-- Su definición es
--    def reverseAux : List α → List α → List α
--      | [],    ys => ys
--      | x::xs, ys => reverseAux xs (x::ys)
--
--    def reverse (xs : List α) : List α :=
--      reverseAux xs []
--
-- Los siguientes lemas caracterizan su comportamiento
--    reverseAux_nil : reverseAux [] ys = ys
--    reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys)
--
-- Una definición alternativa es
--    def reverse2 : List α → List α
--      | []        => []
--      | (x :: xs) => reverse2 xs ++ [x]
--
-- Demostrar que las dos definiciones son equivalentes; es decir,
--    reverse xs = reverse2 xs
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Es consecuencia del siguiente lema auxiliar
--    (∀ xs, ys)[reverseAux xs ys = (reverse2 xs) ++ ys]
-- En efecto,
--    reverse xs = reverseAux xs []
--               = reverse2 xs ++ []    [por el lema auxiliar]
--               = reverse2 xs
--
-- El lema auxiliar se demuestra por inducción en xs.
--
-- Caso base: Supongamos que xs = []. Entonces,
--    reverseAux xs ys = reverseAux [] ys
--                     = ys
--                     = [] ++ ys
--                     = reverse2 [] ++ ys
--                     = reverse2 xs ++ ys
--
-- Paso de inducción: Supongamos que xs = a::as y la hipótesis de
-- inducción (HI):
--    (∀ ys)[reverseAux as ys = reverse2 as ++ ys]
-- Entonces,
--    reverseAux xs ys = reverseAux (a :: as) ys
--                     = reverseAux as (a :: ys)
--                     = reverse2 as ++ (a :: ys)   [por HI]
--                     = reverse2 as ++ ([a] ++ ys)
--                     = (reverse2 as ++ [a]) ++ ys
--                     = reverse2 (a :: as) ++ ys
--                     = reverse2 xs ++ ys

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.List.Basic
open List

variable {α : Type}
variable (x : α)
variable (xs ys : List α)

-- Definición y reglas de simplificación de reverse2
-- =================================================

def reverse2 : List α → List α
  | []        => []
  | (x :: xs) => reverse2 xs ++ [x]

@[simp]
lemma reverse2_nil :
  reverse2 ([] : List α) = [] :=
  rfl

@[simp]
lemma reverse2_cons :
  reverse2 (x :: xs) = reverse2 xs ++ [x] :=
  rfl

-- Lema auxiliar: reverseAux xs ys = (reverse2 xs) ++ ys
-- ======================================================

-- 1ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := reverseAux_nil
       _ = [] ++ ys                   := (nil_append ys).symm
       _ = reverse2 [] ++ ys          := congrArg (. ++ ys) reverse2_nil.symm
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := reverseAux_cons
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := congrArg (reverse2 as ++ .) singleton_append
       _ = (reverse2 as ++ [a]) ++ ys := (append_assoc (reverse2 as) [a] ys).symm
       _ = reverse2 (a :: as) ++ ys   := congrArg (. ++ ys) (reverse2_cons a as).symm

-- 2ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by rw [reverseAux_nil]
       _ = [] ++ ys                   := by rw [nil_append]
       _ = reverse2 [] ++ ys          := by rw [reverse2_nil]
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by rw [reverseAux_cons]
       _ = reverse2 as ++ (a :: ys)   := by rw [(HI (a :: ys))]
       _ = reverse2 as ++ ([a] ++ ys) := by rw [singleton_append]
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := by rw [reverse2_cons]

-- 3ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                := rfl
       _ = [] ++ ys          := by rfl
       _ = reverse2 [] ++ ys := rfl
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := rfl
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := rfl
       _ = (reverse2 as ++ [a]) ++ ys := by rw [append_assoc]
       _ = reverse2 (a :: as) ++ ys   := rfl

-- 3ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    calc reverseAux [] ys
         = ys                         := by simp
       _ = [] ++ ys                   := by simp
       _ = reverse2 [] ++ ys          := by simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 as ++ ([a] ++ ys) := by simp
       _ = (reverse2 as ++ [a]) ++ ys := by simp
       _ = reverse2 (a :: as) ++ ys   := by simp

-- 4ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    calc reverseAux (a :: as) ys
         = reverseAux as (a :: ys)    := by simp
       _ = reverse2 as ++ (a :: ys)   := (HI (a :: ys))
       _ = reverse2 (a :: as) ++ ys   := by simp

-- 5ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    simp
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    simp [HI (a :: ys)]

-- 6ª demostración del lema auxiliar
-- =================================

example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by induction' xs generalizing ys <;> simp [*]

-- 7ª demostración del lema auxiliar
example :
  reverseAux xs ys = (reverse2 xs) ++ ys :=
by
  induction' xs with a as HI generalizing ys
  . -- ys : List α
    -- ⊢ reverseAux [] ys = reverse2 [] ++ ys
    rw [reverseAux_nil]
    -- ⊢ ys = reverse2 [] ++ ys
    rw [reverse2_nil]
    -- ⊢ ys = [] ++ ys
    rw [nil_append]
  . -- a : α
    -- as : List α
    -- HI : ∀ (ys : List α), reverseAux as ys = reverse2 as ++ ys
    -- ys : List α
    -- ⊢ reverseAux (a :: as) ys = reverse2 (a :: as) ++ ys
    rw [reverseAux_cons]
    -- ⊢ reverseAux as (a :: ys) = reverse2 (a :: as) ++ ys
    rw [(HI (a :: ys))]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 (a :: as) ++ ys
    rw [reverse2_cons]
    -- ⊢ reverse2 as ++ a :: ys = (reverse2 as ++ [a]) ++ ys
    rw [append_assoc]
    -- ⊢ reverse2 as ++ a :: ys = reverse2 as ++ ([a] ++ ys)
    rw [singleton_append]

-- 8ª demostración  del lema auxiliar
-- ==================================

@[simp]
lemma reverse2_equiv :
  ∀ xs : List α, ∀ ys, reverseAux xs ys = (reverse2 xs) ++ ys
| []         => by simp
| (a :: as)  => by simp [reverse2_equiv as]

-- Demostraciones del lema principal
-- =================================

-- 1ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
calc reverse xs
     = reverseAux xs []  := rfl
   _ = reverse2 xs ++ [] := by rw [reverse2_equiv]
   _ = reverse2 xs       := by rw [append_nil]

-- 2ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
by simp [reverse2_equiv, reverse]

-- 3ª demostración
-- ===============

example : reverse xs = reverse2 xs :=
by simp [reverse]

-- Lemas usados
-- ============

-- variable (ys zs : List α)
-- #check (append_assoc xs ys zs : (xs ++ ys) ++ zs = xs ++ (ys ++ zs))
-- #check (append_nil xs : xs ++ [] = xs)
-- #check (nil_append xs : [] ++ xs = xs)
-- #check (reverse xs = reverseAux xs [])
-- #check (reverseAux_cons : reverseAux (x::xs) ys = reverseAux xs (x::ys))
-- #check (reverseAux_nil : reverseAux [] ys = ys)
-- #check (singleton_append : [x] ++ ys = x :: ys)
