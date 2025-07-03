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
    -- Helper function to try proving nonzero hypotheses
    let tryNonzeroProof : TacticM Unit := do
      try
        evalTactic (← `(tactic| assumption))
      catch _ =>
        try
          evalTactic (← `(tactic| apply ne_of_gt; assumption))
        catch _ =>
          try
            evalTactic (← `(tactic| norm_num))
          catch _ =>
            try
              evalTactic (← `(tactic| exact Nat.succ_ne_zero _))
            catch _ =>
              throwError "Could not prove nonzero condition"

    -- Helper function to apply multiplication cancellation with a given rule
    let tryMulCancel (rule : TSyntax `tactic) : TacticM Bool := do
      try
        evalTactic rule
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Try simplification for special cases first
    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero, ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Try direct application (no rewrite needed)
    if ← tryMulCancel (← `(tactic| apply ENNReal.mul_div_mul_right)) then return
    if ← tryMulCancel (← `(tactic| apply ENNReal.mul_div_mul_left)) then return

    -- Try with rewrite first, then application
    try
      evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      if ← tryMulCancel (← `(tactic| apply ENNReal.mul_div_mul_right)) then return
      if ← tryMulCancel (← `(tactic| apply ENNReal.mul_div_mul_left)) then return
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
  -- The goal is: 3 * 2 / (5 * 2) = 3 / 5 (cast multiplication has been simplified)
  exact ENNReal.mul_div_mul_right (↑3) (↑5) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_two : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

lemma ennreal_div_cancel_three_manual : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  -- The goal is: 4 * 3 / (7 * 3) = 4 / 7 (cast multiplication has been simplified)
  exact ENNReal.mul_div_mul_right (↑4) (↑7) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_three : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  ennreal_mul_cancel

-- =============================================================================
-- EXAMPLES WITH COMMUTATIVE MULTIPLICATION
-- =============================================================================

lemma ennreal_div_cancel_comm_manual {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_comm {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

-- =============================================================================
-- EDGE CASES
-- =============================================================================

lemma ennreal_div_cancel_zero_num_manual {b c : ℕ} (_hc : c ≠ 0) : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [Nat.cast_zero]
  rw [zero_mul]
  rw [ENNReal.zero_div, ENNReal.zero_div]

lemma ennreal_div_cancel_zero_num {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by
  ennreal_mul_cancel

lemma ennreal_div_cancel_one_manual {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_one {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by
  ennreal_mul_cancel



end TestSuite

end ENNRealArith
