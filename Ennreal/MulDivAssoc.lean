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

    -- Helper function to try a rewrite pattern with optional follow-up tactics
    let tryRewritePattern (rewrites : TSyntax `tactic) (followUp : List (TSyntax `tactic) := []) : TacticM Bool := do
      try
        evalTactic rewrites
        for tac in followUp do
          evalTactic tac
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Helper function to try div_mul_cancel with non-zero proofs
    let tryDivMulCancel : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [ENNReal.div_mul_cancel]))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Try patterns in order of likelihood (most common first for efficiency)

    -- 1. Simple rewrites (most common cases)
    if ← tryRewritePattern (← `(tactic| rw [mul_div])) then return
    if ← tryRewritePattern (← `(tactic| rw [← mul_div])) then return

    -- 2. Rewrites with normalization (common for casting)
    if ← tryRewritePattern (← `(tactic| rw [mul_div])) [← `(tactic| norm_cast)] then return
    if ← tryRewritePattern (← `(tactic| rw [← mul_div])) [← `(tactic| norm_cast)] then return

    -- 3. Complex rewrites (for chained operations)
    if ← tryRewritePattern (← `(tactic| rw [mul_div, mul_assoc])) then return
    if ← tryRewritePattern (← `(tactic| rw [← mul_div, ← mul_assoc])) then return

    -- 4. Division cancellation patterns (specialized cases)
    if ← tryDivMulCancel then return

    -- 5. General simplification as fallback
    if ← tryRewritePattern (← `(tactic| simp only [mul_div, mul_assoc, one_mul, mul_one])) then return

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
  rw [mul_div]
  norm_cast

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
