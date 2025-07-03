/-
Multiplication-division associativity tactics for ENNReal arithmetic.
Handles patterns like (a * (b / c) = (a * b) / c).
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
-- MULTIPLICATION-DIVISION ASSOCIATIVITY TACTIC
-- =============================================================================

-- Multiplication-division associativity patterns (a * (b / c) = (a * b) / c)
syntax "ennreal_mul_div_assoc" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| rw [mul_div]))
      return
    catch _ => pure ()

    try
      evalTactic (← `(tactic| rw [← mul_div]))
      return
    catch _ => pure ()

    throwError "ennreal_mul_div_assoc could not solve the goal"

-- =============================================================================
-- TEST SUITE: MULTIPLICATION-DIVISION ASSOCIATIVITY EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- BASIC MULTIPLICATION-DIVISION ASSOCIATIVITY
-- =============================================================================

lemma ennreal_mul_div_assoc_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_assoc_basic {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_assoc_reverse_manual {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  rw [← mul_div]

lemma ennreal_mul_div_assoc_reverse {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

-- =============================================================================
-- SPECIFIC EXAMPLES WITH CONCRETE NUMBERS
-- =============================================================================

lemma ennreal_mul_div_two_three_five_manual : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_two_three_five : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_four_seven_manual : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_four_seven : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_mul_div_assoc

-- =============================================================================
-- WITH CASTING SIMPLIFICATION
-- =============================================================================

lemma ennreal_mul_div_cast_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  rw [mul_div, ← ENNReal.coe_mul]

lemma ennreal_mul_div_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- =============================================================================
-- CHAINED OPERATIONS
-- =============================================================================

lemma ennreal_mul_div_chain_manual {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  rw [mul_div, mul_assoc]

lemma ennreal_mul_div_chain {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  ennreal_mul_div_assoc

-- =============================================================================
-- WITH ONE VALUES
-- =============================================================================

lemma ennreal_mul_div_one_manual {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  rw [mul_div]

lemma ennreal_mul_div_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  ennreal_mul_div_assoc

lemma ennreal_one_mul_div_manual {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_one_mul_div {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- =============================================================================
-- RECIPROCAL PATTERNS
-- =============================================================================

lemma ennreal_div_mul_cancel_manual {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  rw [ENNReal.div_mul_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

lemma ennreal_div_mul_cancel {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  ennreal_mul_div_assoc

end TestSuite

end ENNRealArith
