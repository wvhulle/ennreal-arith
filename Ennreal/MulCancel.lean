/-
Multiplication cancellation tactics for ENNReal arithmetic.
Handles patterns like (a*c / b*c = a / b) with non-zero hypotheses.
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
-- MULTIPLICATION CANCELLATION TACTIC
-- =============================================================================

-- Multiplication cancellation patterns (a*c / b*c = a / b)
syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
  let goal ← getMainGoal
  goal.withContext do
    -- Try with rewrite first (for goals like ↑(a*c) / ↑(b*c) = ↑a / ↑b)
    try
      evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      evalTactic (← `(tactic| assumption))
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      return
    catch _ => pure ()

    -- Try with rewrite + positivity conversion
    try
      evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      evalTactic (← `(tactic| apply ne_of_gt))
      evalTactic (← `(tactic| assumption))
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      return
    catch _ => pure ()

    -- Try without rewrite (for goals already in the form ↑a * ↑c / (↑b * ↑c) = ↑a / ↑b)
    try
      evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      evalTactic (← `(tactic| assumption))
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      return
    catch _ => pure ()

    try
      evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      evalTactic (← `(tactic| apply ne_of_gt))
      evalTactic (← `(tactic| assumption))
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      return
    catch _ => pure ()

    throwError "ennreal_mul_cancel could not solve the goal"

-- =============================================================================
-- TEST SUITE: MULTIPLICATION CANCELLATION EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- MULTIPLICATION CANCELLATION WITH NONZERO HYPOTHESES
-- =============================================================================

lemma ennreal_div_cancel_mul_manual_ne_zero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_mul_ne_zero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

lemma ennreal_div_cancel_mul_manual_pos {a b c : ℕ} (hc_pos : 0 < c) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt hc_pos))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_mul_pos {a b c : ℕ} (hc_pos : 0 < c) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

-- =============================================================================
-- SPECIFIC EXAMPLES WITH CONCRETE NUMBERS
-- =============================================================================

lemma ennreal_div_cancel_two_manual : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑3) (↑5) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_two : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

lemma ennreal_div_cancel_three_manual : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑4) (↑7) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_three : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  ennreal_mul_cancel

-- =============================================================================
-- EXAMPLES WITH COMMUTATIVE MULTIPLICATION
-- =============================================================================

lemma ennreal_div_cancel_comm_manual {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [mul_comm ↑c ↑a, mul_comm ↑c ↑b]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_comm {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

-- =============================================================================
-- EDGE CASES
-- =============================================================================

lemma ennreal_div_cancel_zero_num_manual {b c : ℕ} (hc : c ≠ 0) : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑0) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_zero_num {b c : ℕ} (hc : c ≠ 0) : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by
  ennreal_mul_cancel

lemma ennreal_div_cancel_one_manual {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_one {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

end TestSuite

end ENNRealArith
