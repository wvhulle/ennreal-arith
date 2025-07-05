import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_mul_div_assoc" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do
    -- First try the most general approach with simp
    try
      evalTactic (← `(tactic| simp only [mul_div, div_mul_eq_mul_div, ENNReal.mul_comm_div, 
                                        mul_assoc, one_mul, mul_one, Nat.cast_mul]))
      if (← getUnsolvedGoals).isEmpty then return
      -- Try norm_cast if simp didn't fully solve
      evalTactic (← `(tactic| norm_cast))
      if (← getUnsolvedGoals).isEmpty then return
      -- Try norm_num for concrete cases
      evalTactic (← `(tactic| norm_num))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    
    -- Try basic rewrites in the most common direction
    let basicPatterns := [
      ← `(tactic| rw [mul_div]),              -- a * (b / c) = (a * b) / c
      ← `(tactic| rw [div_mul_eq_mul_div]),   -- (a / b) * c = (a * c) / b
      ← `(tactic| rw [← mul_div]),            -- reverse direction if needed
      ← `(tactic| rw [← div_mul_eq_mul_div])  -- reverse direction if needed
    ]
    
    for pattern in basicPatterns do
      try
        evalTactic pattern
        -- Try to normalize if needed
        try evalTactic (← `(tactic| norm_cast))
        catch _ => pure ()
        if (← getUnsolvedGoals).isEmpty then return
      catch _ => continue
    
    -- Handle special case: division multiplication cancellation
    -- First check if it's the exact pattern we're looking for
    try
      -- For the specific pattern 1 / x * x = 1, we can use simp
      evalTactic (← `(tactic| simp only [ENNReal.div_mul_cancel]))
      -- May need to prove conditions
      let remainingGoals ← getUnsolvedGoals
      for goal in remainingGoals do
        goal.withContext do
          try
            -- Try to prove ≠ 0
            evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
            evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
            evalTactic (← `(tactic| assumption))
          catch _ =>
            try
              -- Try to prove ≠ ⊤
              evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
            catch _ =>
              -- Last resort
              evalTactic (← `(tactic| assumption))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    
    -- Handle division by self pattern (which can arise from simplification)
    try
      evalTactic (← `(tactic| apply ENNReal.div_self))
      -- Prove ≠ 0
      try
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        evalTactic (← `(tactic| assumption))
      catch _ =>
        evalTactic (← `(tactic| assumption))
      -- Prove ≠ ⊤
      try
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      catch _ =>
        evalTactic (← `(tactic| assumption))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    throwError "ennreal_mul_div_assoc could not solve the goal"


section TestSuite


lemma ennreal_mul_div_assoc_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_assoc_basic {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_assoc_reverse_manual {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  rw [← mul_div]

lemma ennreal_mul_div_assoc_reverse {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_two_three_five_manual : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_two_three_five : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_four_seven_manual : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_four_seven : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_cast_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  rw [mul_div]
  norm_cast

lemma ennreal_mul_div_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_chain_manual {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  rw [mul_div, mul_assoc]

lemma ennreal_mul_div_chain {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_one_manual {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  rw [mul_div]

lemma ennreal_mul_div_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  ennreal_mul_div_assoc

lemma ennreal_one_mul_div_manual {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_one_mul_div {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_div_mul_cancel_manual {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  rw [ENNReal.div_mul_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

lemma ennreal_div_mul_cancel {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  ennreal_mul_div_assoc


lemma ennreal_div_mul_right_manual {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  rw [ENNReal.mul_comm_div]
  rw [mul_div]

lemma ennreal_div_mul_right {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_div_mul_concrete : ((↑6 : ENNReal) / (↑2 : ENNReal)) * (↑3 : ENNReal) = (↑6 * ↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_mul_div_assoc

end TestSuite

end ENNRealArith
