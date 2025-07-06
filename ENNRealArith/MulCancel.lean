import ENNRealArith.Common

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/
syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
  let goal ← getMainGoal
  goal.withContext do

    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero,
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Use the common nonzero proof function

    let tryCancel : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      catch _ => pure ()

      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => pure ()

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

-- Division cancellation lemmas
lemma test_division_cancellation_right_nonzero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

lemma test_division_cancellation_right_positive {a b c : ℕ} (hc_pos : 0 < c) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  have hc : c ≠ 0 := ne_of_gt hc_pos
  ennreal_mul_cancel

-- Left cancellation
lemma test_division_cancellation_left {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

-- Concrete cancellation examples
lemma test_division_cancellation_concrete_factor_two : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

lemma test_division_cancellation_concrete_factor_three : (↑(4 * 3) : ENNReal) / (↑(7 * 3)) = (↑4) / (↑7) := by
  ennreal_mul_cancel

-- Special cases
lemma test_division_cancellation_zero_numerator {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by
  ennreal_mul_cancel

lemma test_division_cancellation_factor_one {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by
  ennreal_mul_cancel



end TestSuite

end ENNRealArith
