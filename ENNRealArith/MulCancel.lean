import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
  let goal ← getMainGoal
  goal.withContext do
    -- First try simple cases with simp
    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero, 
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    
    -- Optimized nonzero proof that tries tactics in order of likelihood
    let tryNonzeroProof : TacticM Unit := do
      -- Most common: hypothesis already in context
      try evalTactic (← `(tactic| assumption)); return
      catch _ => pure ()
      -- Second: positive implies nonzero (common in Lean proofs)
      try evalTactic (← `(tactic| apply ne_of_gt; assumption)); return
      catch _ => pure ()
      -- Third: concrete numbers
      try evalTactic (← `(tactic| norm_num)); return  
      catch _ => pure ()
      -- Fourth: successor pattern
      try evalTactic (← `(tactic| exact Nat.succ_ne_zero _)); return
      catch _ => throwError "Could not prove nonzero condition"

    -- Single function that handles both left and right cancellation
    let tryCancel : TacticM Bool := do
      try
        -- Ensure we have the right form
        evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      catch _ => pure ()
      
      -- Try right cancellation first (more common)
      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => pure ()
      
      -- If right didn't work, try left
      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_left))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    if ← tryCancel then return
    
    throwError "ennreal_mul_cancel could not solve the goal"

section TestSuite

lemma ennreal_div_cancel_mul_manual_ne_zero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_mul_ne_zero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

lemma ennreal_div_cancel_mul_manual_pos {a b c : ℕ} (hc_pos : 0 < c) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt hc_pos))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_mul_pos {a b c : ℕ} (hc_pos : 0 < c) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  have hc : c ≠ 0 := ne_of_gt hc_pos
  ennreal_mul_cancel



lemma ennreal_div_cancel_two_manual : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  exact ENNReal.mul_div_mul_right (↑3) (↑5) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_two : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

lemma ennreal_div_cancel_three_manual : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  exact ENNReal.mul_div_mul_right (↑4) (↑7) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_cancel_three : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  ennreal_mul_cancel



lemma ennreal_div_cancel_comm_manual {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  rw [Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left (↑a) (↑b) (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr hc)) ENNReal.coe_ne_top

lemma ennreal_div_cancel_comm {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  ennreal_mul_cancel



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
