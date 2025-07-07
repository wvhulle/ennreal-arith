import ENNRealArith.Common

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/-!
# Core ENNReal Arithmetic Tactics

This module contains the fundamental arithmetic tactics for ENNReal:
- Basic simplification (`ennreal_basic_simp`)
- Division by self patterns (`ennreal_div_self`)
- Multiplication cancellation (`ennreal_mul_cancel`)

These form the foundation for more complex ENNReal arithmetic automation.
-/

-- =============================================
-- BASIC SIMPLIFICATION TACTIC
-- =============================================

/--
Tactic for basic ENNReal simplifications using norm_num, norm_cast, and simp.
Tries various combinations of these tactics to solve simple arithmetic goals.
-/
syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  if ← tryBasicComputation then return

  if ← tryTactic (← `(tactic| simp)) then return

  let tacticSequences := [
    [← `(tactic| norm_cast), ← `(tactic| norm_num)],
    [← `(tactic| simp only [add_zero, zero_add, inv_eq_one_div])],
    [← `(tactic| simp only [add_zero, zero_add]), ← `(tactic| norm_num)],
    [← `(tactic| rw [ENNReal.div_eq_div_iff]), ← `(tactic| all_goals norm_num)]
  ]

  for sequence in tacticSequences do
    if ← tryTacticSequence sequence then return

  throwError "ennreal_basic_simp could not solve the goal"

-- =============================================
-- DIVISION BY SELF TACTIC
-- =============================================

/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`.
-/
syntax "ennreal_div_self" : tactic

elab_rules : tactic | `(tactic| ennreal_div_self) =>  do



  try
    evalTactic (← `(tactic| apply ENNReal.div_self))
    evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
    evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
    tryNonzeroProof
    evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    if (← getUnsolvedGoals).isEmpty then return
  catch _ => pure ()



  throwError "ennreal_div_self could not solve the goal"

-- =============================================
-- MULTIPLICATION CANCELLATION TACTIC
-- =============================================

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

    let attemptCancellation : TacticM Bool := do
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

    if ← attemptCancellation then return

    throwError "ennreal_mul_cancel could not solve the goal"

-- =============================================
-- TEST SUITES
-- =============================================

section BasicSimpTests

-- Essential identity tests
lemma test_addition_right_identity {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by ennreal_basic_simp
lemma test_multiplication_right_identity {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by ennreal_basic_simp
lemma test_division_by_one {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by ennreal_basic_simp

-- Key absorption properties
lemma test_multiplication_zero_absorbing {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by ennreal_basic_simp
lemma test_zero_divided_by_any {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by ennreal_basic_simp

-- Core concrete examples
lemma test_addition_concrete : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_basic_simp
lemma test_multiplication_concrete : (↑2 : ENNReal) * ↑3 = ↑6 := by ennreal_basic_simp

-- Cast preservation (essential for interoperability)
lemma test_addition_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by ennreal_basic_simp
lemma test_multiplication_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by ennreal_basic_simp

end BasicSimpTests

section DivSelfTests


-- Currently fails!

-- Core division by self functionality
lemma test_division_self_nonzero {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_div_self

lemma test_division_self_nonzero_manual {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  apply ENNReal.div_self
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by assumption))
  · exact ENNReal.coe_ne_top

lemma test_division_self_successor {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_div_self

-- Concrete examples
lemma test_division_self_concrete : (↑2 : ENNReal) / ↑2 = 1 := by ennreal_div_self

end DivSelfTests

section MulCancelTests

-- Core cancellation functionality
lemma test_division_cancellation_right {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel
lemma test_division_cancellation_left {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by ennreal_mul_cancel

-- Concrete examples
lemma test_division_cancellation_concrete : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

-- Special cases
lemma test_division_cancellation_zero_numerator {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by ennreal_mul_cancel

end MulCancelTests

end ENNRealArith

#lint
