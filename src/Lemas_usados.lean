-- Lemas_usados.lean
-- Lemas usados.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 25-agosto-2023
-- ---------------------------------------------------------------------

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Topology.MetricSpace.Basic

-- Números naturales
-- =================

section naturales
variable (x y z k m n : ℕ)
open Nat
#check (_root_.dvd_antisymm : m ∣ n → n ∣ m → m = n)
#check (dvd_add : x ∣ y → x ∣ z → x ∣ y + z)
#check (dvd_factorial : 0 < k → k ≤ n → k ∣ n !)
#check (dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n)
#check (dvd_mul_left x y : x ∣ y * x)
#check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
#check (dvd_mul_of_dvd_right : x ∣ y → ∀ (c : ℕ), x ∣ c * y)
#check (dvd_mul_right x y : x ∣ x * y)
#check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
#check (Dvd.intro k : m * k = n → m ∣ n)
#check (factorial_pos n: n ! > 0)
#check (gcd_comm m n : gcd m n = gcd n m)
#check (gcd_dvd_left  m n: gcd m n ∣ m)
#check (gcd_dvd_right m n : gcd m n ∣ n)
#check (minFac_dvd n : minFac n ∣ n)
#check (minFac_pos n : 0 < minFac n)
#check (minFac_prime : n ≠ 1 → Nat.Prime (minFac n))
#check (Nat.dvd_add_iff_right : k ∣ m → (k ∣ n ↔ k ∣ m + n))
#check (Nat.dvd_one : n ∣ 1 ↔ n = 1)
#check (Nat.lt_add_of_pos_left : 0 < k → n < k + n)
#check (Nat.ne_of_gt : k < n → n ≠ k)
#check (Nat.Prime.not_dvd_one : Nat.Prime n → ¬n ∣ 1)
end naturales

-- Números reales
-- ==============

section reales
open Real
variable (a b c d x y : ℝ)
#check (Left.self_le_neg : x ≤ 0 → x ≤ -x)
#check (abs_add a b : |a + b| ≤ |a| + |b|)
#check (abs_le' : |a| ≤ b ↔ a ≤ b ∧ -a ≤ b)
#check (abs_lt: |a| < b ↔ -b < a ∧ a < b)
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_nonneg a : 0 ≤ |a|)
#check (abs_of_neg : x < 0 → |x| = -x)
#check (abs_of_nonneg : 0 ≤ x → |x| = x)
#check (abs_sub_abs_le_abs_sub a b : |a| - |b| ≤ |a - b|)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : b ≤ c → ∀ (a : ℝ), a + b ≤ a + c)
#check (add_le_add_right : b ≤ c → ∀ (a : ℝ),  b + a ≤ c + a)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : b < c → ∀ (a : ℝ), b + a < c + a)
#check (add_neg_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_sub_cancel a b : a + b - b = a)
#check (div_mul_cancel a : b ≠ 0 → (a / b) * b = a)
#check (eq_neg_of_add_eq_zero_left : x + y = 0 → x = -y)
#check (eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (exp_pos a : 0 < exp a)
#check (half_lt_self : 0 < a → a / 2 < a)
#check (half_pos : 0 < a → 0 < a / 2)
#check (le_abs_self x : x ≤ |x|)
#check (le_add_of_nonneg_right : 0 ≤ b → a ≤ a + b)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)
#check (le_div_iff : 0 < c → (a ≤ b / c ↔ a * c ≤ b))
#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check (le_neg_self_iff : x ≤ -x ↔ x ≤ 0)
#check (le_of_eq : a = b → a ≤ b)
#check (le_of_lt : x < y → x ≤ y)
#check (le_of_not_ge : ¬x ≥ y → x ≤ y)
#check (le_of_not_gt : ¬a > b → a ≤ b)
#check (le_or_gt x y : x ≤ y ∨ x > y)
#check (le_refl a : a ≤ a)
#check (log_le_log' : 0 < a → a ≤ b → log a ≤ log b)
#check (lt_abs : x < |y| ↔ x < y ∨ x < -y)
#check (lt_asymm : a < b → ¬b < a)
#check (lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b)
#check (lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a)
#check (lt_irrefl a : ¬a < a)
#check (lt_neg : a < -b ↔ b < -a)
#check (lt_of_le_of_ne : a ≤ b → a ≠ b → a < b)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_le_of_ne : a ≤ b → a ≠ b → a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (lt_of_not_le : ¬b ≤ a → a < b)
#check (lt_trans : a < b → b < c → a < c)
#check (lt_trichotomy a b : a < b ∨ a = b ∨ b < a)
#check (max_comm a b : max a b = max b a)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)
#check (min_add_add_right a b c : min (a + c) (b + c) = min a b + c)
#check (min_assoc a b c : min (min a b) c = min a (min b c))
#check (min_comm a b : min a b = min b a)
#check (min_eq_left : a ≤ b → min a b = a)
#check (min_eq_right : b ≤ a → min a b = b)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (mul_comm a b : a * b = b * a)
#check (mul_div_cancel' a : b ≠ 0 → b * (a / b) = a)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_right : 0 < a → (b * a ≤ c * a ↔ b ≤ c))
#check (mul_left_cancel₀ : a ≠ 0 → a * b = a * c → b = c)
#check (mul_lt_mul_left : 0 < a → (a * b < a * c ↔ b < c))
#check (mul_lt_mul_right : 0 < a → (b * a < c * a ↔ b < c))
#check (mul_neg a b : a * -b = -(a * b))
#check (mul_right_inj' :  a ≠ 0 → (a * b = a * c ↔ b = c))
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
#check (mul_two a : a * 2 = a + a)
#check (ne_comm : a ≠ b ↔ b ≠ a)
#check (neg_add x y : -(x + y) = -x + -y)
#check (neg_add_self a : -a + a = 0)
#check (neg_le_abs_self x : -x ≤ |x|)
#check (neg_mul_neg a b : -a * -b = a * b)
#check (nonneg_of_mul_nonneg_left : 0 ≤ a * b → 0 < b → 0 ≤ a)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (pow_eq_zero : ∀ {n : ℕ}, a ^ n = 0 → a = 0)
#check (pow_two a : a ^ 2 = a * a)
#check (pow_two_nonneg a : 0 ≤ a ^ 2)
#check (sq_eq_one_iff : x ^ 2 = 1 ↔ x = 1 ∨ x = -1)
#check (sq_eq_sq_iff_eq_or_eq_neg : x ^ 2 = y ^ 2 ↔ x = y ∨ x = -y)
#check (sq_nonneg a : 0 ≤ a ^ 2)
#check (sub_add_cancel a b : a - b + b = a)
#check (sub_eq_zero : x - y = 0 ↔ x = y)
#check (sub_le_sub_left : a ≤ b → ∀ (c : ℝ), c - b ≤ c - a)
#check (sub_le_sub_right : a ≤ b → ∀ (c : ℝ), a - c ≤ b - c)
#check (sub_sq a b : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2)
#check (two_mul a : 2 * a = a + a)
#check (two_mul_le_add_sq a b : 2 * a * b ≤ a ^ 2 + b ^ 2)
#check (zero_lt_one : 0 < 1)
#check (zero_lt_two : 0 < 2)
end reales

-- Anillos
-- =======

section anillos
variable {R : Type _} [Ring R]
variable (a b c : R)
#check (add_assoc a b c : (a + b) + c = a + (b + c))
#check (add_comm a b : a + b = b + a)
#check (add_eq_zero_iff_eq_neg : a + b = 0 ↔ a = -b)
#check (add_left_cancel : a + b = a + c → b = c)
#check (add_left_neg a : -a + a = 0)
#check (add_mul a b c : (a + b) * c = a * c + b * c)
#check (add_neg_cancel_right a b : (a + b) + -b = a)
#check (add_neg_self a : a + -a = 0)
#check (add_right_cancel : a + b = c + b → a = c)
#check (add_right_neg a : a + -a = 0)
#check (add_zero a : a + 0 = a)
#check (mul_add a b c : a * (b + c) = a * b + a * c)
#check (mul_zero a : a * 0 = 0)
#check (neg_add_cancel_left a b : -a + (a + b) = b)
#check (neg_eq_iff_add_eq_zero : -a = b ↔ a + b = 0)
#check (neg_eq_of_add_eq_zero_left : a + b = 0 → -b = a)
#check (neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b)
#check (neg_neg a : -(-a) = a)
#check (neg_zero : -0 = 0)
#check (one_add_one_eq_two : (1 : R) + 1 = 2)
#check (sub_add_cancel a b : a - b + b = a)
#check (sub_eq_add_neg a b : a - b = a + -b)
#check (sub_mul a b c : (a - b) * c = a * c - b * c)
#check (sub_self a : a - a = 0)
#check (two_mul a : 2 * a = a + a)
#check (zero_add a : 0 + a = a)
#check (zero_mul a : 0 * a = 0)
end anillos

-- Grupos
-- ======

section grupos
variable {G : Type _} [Group G]
variable (a b c : G)
#check (inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b)
#check (mul_assoc a b c : (a * b) * c = a * (b * c))
#check (mul_inv_self a : a * a⁻¹ = 1)
#check (mul_inv_rev a b : (a * b)⁻¹ = b⁻¹ * a⁻¹)
#check (mul_left_inv a : a⁻¹  * a = 1)
#check (mul_one a : a * 1 = a)
#check (mul_right_inv a : a * a⁻¹ = 1)
#check (one_mul a : 1 * a = a)
end grupos

-- Retículos
-- =========

section reticulos
variable {α : Type _} [Lattice α]
variable (x y z : α)
#check (inf_assoc : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z))
#check (inf_comm : x ⊓ y = y ⊓ x)
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_of_left_le : x ≤ z → x ⊓ y ≤ z)
#check (inf_le_of_right_le : y ≤ z → x ⊓ y ≤ z)
#check (inf_le_right : x ⊓ y ≤ y)
#check (inf_sup_self : x ⊓ (x ⊔ y) = x)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check (le_rfl : x ≤ x)
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_of_le_left : z ≤ x → z ≤ x ⊔ y)
#check (le_sup_of_le_right : z ≤ y → z ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (sup_assoc : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z))
#check (sup_comm : x ⊔ y = y ⊔ x)
#check (sup_inf_self : x ⊔ (x ⊓ y) = x)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
end reticulos

-- AnillosOrdenados
-- ================

section AnillosOrdenados
variable {R : Type _} [StrictOrderedRing R]
variable (a b c : R)
#check (add_le_add_right : b ≤ c → ∀ (a : R),  b + a ≤ c + a)
#check (mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c)
#check (mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check (sub_le_sub_right : a ≤ b → ∀ (c : R), a - c ≤ b - c)
#check (sub_nonneg : 0 ≤ a - b ↔ b ≤ a)
end AnillosOrdenados

-- Espacios métricos
-- =================

section EspacioMetrico
variable {X : Type _} [MetricSpace X]
variable (x y z : X)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_nonneg : 0 ≤ dist x y)
#check (dist_self x : dist x x = 0)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
end EspacioMetrico

-- Conjuntos
-- =========

section Conjuntos
open Set
variable {α : Type _}
variable (r s t : Set α)
#check (Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t)
end Conjuntos

-- Órdenes parciales
-- =================

section OrdenParcial
variable {α : Type _} [PartialOrder α]
variable (a b c : α)
#check (irrefl a : ¬a < a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_trans : a < b → b < c → a < c)
#check (monotone_const : Monotone fun _ : ℝ ↦ c)
end OrdenParcial

-- Funciones
-- =========

section Funciones
open Function
variable {α : Type _} {β : Type _} {γ : Type _}
variable {f : α → β} {g : β → γ}
variable (c : ℝ)
#check (Injective.comp : Injective g → Injective f → Injective (g ∘ f))
#check (Surjective.comp : Surjective g → Surjective f → Surjective (g ∘ f))
#check (add_right_surjective c : Surjective (fun x ↦ x + c))
#check (mul_left_surjective₀ : c ≠ 0 → Surjective (fun x ↦ c * x))
end Funciones

-- Lógica
-- ======

section Logica
variable (p q : Prop)
variable {α : Type _}
variable (P : α → Prop)
#check (absurd : p → ¬p → q)
#check (forall_not_of_not_exists : (¬∃ x, P x) → ∀ x, ¬P x)
#check (not_exists : (¬∃ x, P x) ↔ ∀ (x : α), ¬P x)
#check (not_exists_of_forall_not : (∀ x, P x → q) → (∃ x, P x) → q)
#check (not_imp : ¬(p → q) ↔ p ∧ ¬q)
#check (not_forall : (¬∀ x, P x) ↔ ∃ x, ¬P x)
#check (not_forall_of_exists_not : (∃ x, ¬P x) → ¬∀ x, P x)
#check (not_not_intro : p → ¬¬p)
#check (of_not_not : ¬¬p → p)
#check (Or.inl : p → p ∨ q)
#check (Or.inr : q → p ∨ q)
end Logica
