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
      ← `(tactic| rw [div_mul_eq_mul_div]),
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



    try

      evalTactic (← `(tactic| simp only [ENNReal.div_mul_cancel]))

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

              evalTactic (← `(tactic| assumption))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()


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

-- Multiplication-division associativity lemmas
lemma test_mul_div_associativity_right {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_left {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

-- Concrete associativity examples
lemma test_mul_div_associativity_concrete_2_3_5 : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_concrete_4_1_7 : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_mul_div_assoc

-- Cast preservation
lemma test_mul_div_associativity_preserves_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Chain operations
lemma test_mul_div_associativity_chain {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  ennreal_mul_div_assoc

-- Special cases
lemma test_mul_div_associativity_denominator_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_multiplier_one {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Reciprocal identity
lemma test_reciprocal_multiplication_identity {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  ennreal_mul_div_assoc

-- Division-multiplication associativity
lemma test_div_mul_associativity {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_div_mul_associativity_concrete_6_2_3 : ((↑6 : ENNReal) / (↑2 : ENNReal)) * (↑3 : ENNReal) = (↑6 * ↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_mul_div_assoc

end TestSuite

end ENNRealArith
