-- Reglas de la conjunción
-- =======================

-- Ej. 1. Demostrar que
--    P ∧ Q → Q ∧ P

import tactic            

variables (P Q : Prop)

-- 1ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from and.left h,
have hQ : Q, 
  from and.right h,
show Q ∧ P,  
  from and.intro hQ hP

-- 2ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from h.left,
have hQ : Q, 
  from h.right,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 3ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from h.1,
have hQ : Q, 
  from h.2,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 4ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P := h.1,
have hQ : Q := h.2,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 5ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
show Q ∧ P,  
  from ⟨h.2, h.1⟩

-- 6ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q, ⟨h.2, h.1⟩

-- 7ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ h, ⟨h.2,h.1⟩

-- 8ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
and.comm.mp

-- 9ª demostración
-- =============== 

example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hP hQ,
  split,
  { exact hQ, },
  { exact hP, },
end

-- 10ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
end

-- 11ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

-- 12ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by tauto

-- 13ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by finish

