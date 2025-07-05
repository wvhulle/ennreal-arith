import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv

open ENNReal

namespace ENNRealArith

/-!
# Simp Lemmas for ENNReal Arithmetic

This file contains lemmas marked with `@[simp]` to help the `simp` tactic
simplify ENNReal arithmetic expressions automatically.
-/

section DivisionLemmas


@[simp]
lemma ennreal_nat_div_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 :=
  ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)) ENNReal.coe_ne_top

@[simp]
lemma ennreal_succ_div_self (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 :=
  ennreal_nat_div_self (Nat.succ_ne_zero n)


@[simp]
lemma ennreal_coe_add_one_div_self (n : ℕ) : ((↑n : ENNReal) + 1) / ((↑n : ENNReal) + 1) = 1 := by
  have h : (↑n : ENNReal) + 1 ≠ 0 := by simp
  have h' : (↑n : ENNReal) + 1 ≠ ⊤ := by simp
  exact ENNReal.div_self h h'

end DivisionLemmas

section MultiplicationCancellation

@[simp]
lemma ennreal_nat_mul_div_mul_right {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c) : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b)
    (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc))
    ENNReal.coe_ne_top

@[simp]
lemma ennreal_nat_mul_div_mul_left {a b c : ℕ} (hc : c ≠ 0) :
  (↑(c * a) : ENNReal) / (↑(c * b) : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left (↑a) (↑b)
    (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc))
    ENNReal.coe_ne_top


@[simp]
lemma ennreal_zero_mul_div {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c) : ENNReal) = 0 / (↑b : ENNReal) := by
  simp [Nat.cast_mul, zero_mul, ENNReal.zero_div]

end MultiplicationCancellation

section AssociativityLemmas


@[simp]
lemma ennreal_nat_mul_div_assoc {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div_assoc', Nat.cast_mul]

@[simp]
lemma ennreal_nat_div_mul_assoc {a b c : ℕ} :
  ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑(a * c) : ENNReal) / (↑b : ENNReal) := by
  rw [ENNReal.mul_comm_div, mul_div_assoc', Nat.cast_mul]


@[simp]
lemma ennreal_nat_div_mul_cancel {a : ℕ} (ha : a ≠ 0) :
  (1 / (↑a : ENNReal)) * (↑a : ENNReal) = 1 := by
  rw [ENNReal.div_mul_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

end AssociativityLemmas

section InverseLemmas


-- Note: The default form is already a⁻¹ * b = b / a by definition in ENNReal

@[simp]
lemma ennreal_nat_one_div_inv {a : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ = (↑a : ENNReal) := by
  rw [one_div, inv_inv]

end InverseLemmas

end ENNRealArith
