/-
Inverse pattern tactics for ENNReal arithmetic.
Handles patterns involving division and inverse relationships.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

-- =============================================================================
-- INVERSE PATTERNS TACTIC
-- =============================================================================

-- Inverse patterns (handling division and inverse relationships)
syntax "ennreal_inv_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| rw [ENNReal.div_eq_inv_mul, one_mul, inv_inv]))
      return
    catch _ => pure ()

    throwError "ennreal_inv_patterns could not solve the goal"

-- =============================================================================
-- TEST SUITE: INVERSE PATTERNS EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- BASIC INVERSE PATTERNS
-- =============================================================================

lemma ennreal_inv_div_mul_div_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul]
  simp only [mul_one, inv_inv]
  rw [mul_assoc, mul_comm ↑a, ← mul_assoc]
  rw [← ENNReal.coe_mul]

lemma ennreal_inv_div_mul_div {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- COMPLEX INVERSE PATTERNS
-- =============================================================================

lemma ennreal_complex_inv_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul]
  simp only [mul_one, inv_inv]
  rw [← mul_assoc, mul_comm (↑c)⁻¹, mul_assoc]
  rw [mul_comm ↑a, ← ENNReal.coe_mul]
  rw [mul_comm]

lemma ennreal_complex_inv {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- SIMPLE INVERSE CASES
-- =============================================================================

lemma ennreal_div_eq_inv_mul_manual {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul]

lemma ennreal_div_eq_inv_mul {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  ennreal_inv_patterns


lemma ennreal_one_div_eq_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, one_mul]

lemma ennreal_one_div_eq_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  ennreal_inv_patterns


-- =============================================================================
-- DOUBLE INVERSE PATTERNS
-- =============================================================================

lemma ennreal_inv_inv_manual {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  rw [inv_inv]

lemma ennreal_inv_inv {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_one_div_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  rw [ENNReal.div_eq_inv_mul, one_mul, inv_inv]

lemma ennreal_one_div_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- MULTIPLICATION WITH INVERSES
-- =============================================================================

lemma ennreal_mul_inv_manual {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  rw [← ENNReal.div_eq_inv_mul]

lemma ennreal_mul_inv {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_inv_patterns


lemma ennreal_inv_mul_self_manual {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal)⁻¹ * (↑a : ENNReal) = 1 := by
  rw [← ENNReal.div_eq_inv_mul, ENNReal.div_self]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

lemma ennreal_inv_mul_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal)⁻¹ * (↑a : ENNReal) = 1 := by
  ennreal_inv_patterns

-- =============================================================================
-- SPECIFIC EXAMPLES WITH CONCRETE NUMBERS
-- =============================================================================

lemma ennreal_two_inv_three_manual : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul]
  rw [one_mul, inv_inv]
  rw [mul_div]

lemma ennreal_two_inv_three : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_inv_patterns

end TestSuite

end ENNRealArith
