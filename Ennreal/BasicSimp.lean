/-
Basic simplification tactics for ENNReal arithmetic.
Handles norm_num and norm_cast simplifications.
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
-- BASIC SIMPLIFICATION TACTIC
-- =============================================================================

-- Basic simplifications (norm_num, norm_cast)
syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  let goal ← getMainGoal
  goal.withContext do
    -- Try norm_num first for direct numerical computations
    try
      evalTactic (← `(tactic| norm_num))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Try norm_cast alone - this handles many casting cases completely
    try
      evalTactic (← `(tactic| norm_cast))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Try simp for algebraic identities
    try
      evalTactic (← `(tactic| simp))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Try norm_cast followed by norm_num (for cases where norm_cast leaves numerical goals)
    try
      evalTactic (← `(tactic| norm_cast))
      evalTactic (← `(tactic| norm_num))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Try norm_cast followed by simp
    try
      evalTactic (← `(tactic| norm_cast))
      evalTactic (← `(tactic| simp))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    throwError "ennreal_basic_simp could not solve the goal"

-- =============================================================================
-- TEST SUITE: BASIC SIMPLIFICATION EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- LEVEL 1: TRIVIAL CONSTANT CASES
-- =============================================================================

lemma ennreal_zero_cast_manual : (↑0 : ENNReal) = 0 := by
  norm_cast

lemma ennreal_zero_cast : (↑0 : ENNReal) = 0 := by
  ennreal_basic_simp

lemma ennreal_one_cast_manual : (↑1 : ENNReal) = 1 := by
  norm_cast

lemma ennreal_one_cast : (↑1 : ENNReal) = 1 := by
  ennreal_basic_simp

lemma ennreal_two_cast_manual : (↑2 : ENNReal) = 2 := by
  norm_cast

lemma ennreal_two_cast : (↑2 : ENNReal) = 2 := by
  ennreal_basic_simp

-- =============================================================================
-- LEVEL 2: BASIC IDENTITY OPERATIONS (with 0 and 1)
-- =============================================================================

lemma ennreal_add_zero_manual {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by
  simp only [add_zero]

lemma ennreal_add_zero {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by
  ennreal_basic_simp

lemma ennreal_zero_add_manual {a : ℕ} : 0 + (↑a : ENNReal) = ↑a := by
  simp only [zero_add]

lemma ennreal_zero_add {a : ℕ} : 0 + (↑a : ENNReal) = ↑a := by
  ennreal_basic_simp

lemma ennreal_mul_one_manual {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by
  simp only [mul_one]

lemma ennreal_mul_one {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by
  ennreal_basic_simp

lemma ennreal_one_mul_manual {a : ℕ} : 1 * (↑a : ENNReal) = ↑a := by
  simp only [one_mul]

lemma ennreal_one_mul {a : ℕ} : 1 * (↑a : ENNReal) = ↑a := by
  ennreal_basic_simp

lemma ennreal_mul_zero_manual {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by
  simp only [mul_zero]

lemma ennreal_mul_zero {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by
  ennreal_basic_simp

lemma ennreal_zero_mul_manual {a : ℕ} : 0 * (↑a : ENNReal) = 0 := by
  simp only [zero_mul]

lemma ennreal_zero_mul {a : ℕ} : 0 * (↑a : ENNReal) = 0 := by
  ennreal_basic_simp

lemma ennreal_div_one_manual {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by
  simp only [div_one]

lemma ennreal_div_one {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by
  ennreal_basic_simp

lemma ennreal_zero_div_manual {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by
  simp only [ENNReal.zero_div]

lemma ennreal_zero_div {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by
  ennreal_basic_simp

-- =============================================================================
-- LEVEL 3: BASIC POWER OPERATIONS
-- =============================================================================

lemma ennreal_pow_zero_manual {a : ℕ} : (↑a : ENNReal) ^ 0 = 1 := by
  simp only [pow_zero]

lemma ennreal_pow_zero {a : ℕ} : (↑a : ENNReal) ^ 0 = 1 := by
  ennreal_basic_simp

lemma ennreal_pow_one_manual {a : ℕ} : (↑a : ENNReal) ^ 1 = ↑a := by
  simp only [pow_one]

lemma ennreal_pow_one {a : ℕ} : (↑a : ENNReal) ^ 1 = ↑a := by
  ennreal_basic_simp

lemma ennreal_one_pow_manual {n : ℕ} : (1 : ENNReal) ^ n = 1 := by
  simp only [one_pow]

lemma ennreal_one_pow {n : ℕ} : (1 : ENNReal) ^ n = 1 := by
  ennreal_basic_simp

-- =============================================================================
-- LEVEL 4: CONCRETE ARITHMETIC (specific numbers)
-- =============================================================================

lemma ennreal_add_two_three_manual : (↑2 : ENNReal) + ↑3 = ↑5 := by
  norm_num

lemma ennreal_add_two_three : (↑2 : ENNReal) + ↑3 = ↑5 := by
  ennreal_basic_simp

lemma ennreal_mul_two_three_manual : (↑2 : ENNReal) * ↑3 = ↑6 := by
  norm_num

lemma ennreal_mul_two_three : (↑2 : ENNReal) * ↑3 = ↑6 := by
  ennreal_basic_simp

lemma ennreal_pow_two_three_manual : (↑2 : ENNReal) ^ 3 = ↑8 := by
  norm_num

lemma ennreal_pow_two_three : (↑2 : ENNReal) ^ 3 = ↑8 := by
  ennreal_basic_simp

-- Handle the specific subtraction case that norm_num struggles with
lemma ennreal_sub_five_three_manual : (↑5 : ENNReal) - ↑3 = ↑2 := by
  norm_cast

lemma ennreal_sub_five_three : (↑5 : ENNReal) - ↑3 = ↑2 := by
  ennreal_basic_simp

-- =============================================================================
-- LEVEL 5: BASIC CASTING PRESERVATION (general forms)
-- =============================================================================

lemma ennreal_mul_cast_manual {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by
  norm_cast

lemma ennreal_mul_cast {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by
  ennreal_basic_simp

lemma ennreal_pow_cast_manual {a b : ℕ} : (↑a : ENNReal) ^ b = ↑(a ^ b) := by
  norm_cast

lemma ennreal_pow_cast {a b : ℕ} : (↑a : ENNReal) ^ b = ↑(a ^ b) := by
  ennreal_basic_simp

lemma ennreal_sub_cast_manual {a b : ℕ} : (↑a : ENNReal) - ↑b = ↑(a - b) := by
  norm_cast

lemma ennreal_sub_cast {a b : ℕ} : (↑a : ENNReal) - ↑b = ↑(a - b) := by
  ennreal_basic_simp

-- =============================================================================
-- LEVEL 6: CASTING PRESERVATION (specific examples)
-- =============================================================================

lemma ennreal_cast_add_specific_manual : (↑(2 + 3) : ENNReal) = ↑2 + ↑3 := by
  norm_cast

lemma ennreal_cast_add_specific : (↑(2 + 3) : ENNReal) = ↑2 + ↑3 := by
  ennreal_basic_simp

lemma ennreal_cast_mul_specific_manual : (↑(2 * 3) : ENNReal) = ↑2 * ↑3 := by
  norm_cast

lemma ennreal_cast_mul_specific : (↑(2 * 3) : ENNReal) = ↑2 * ↑3 := by
  ennreal_basic_simp

lemma ennreal_cast_pow_specific_manual : (↑(2 ^ 3) : ENNReal) = ↑2 ^ 3 := by
  norm_cast

lemma ennreal_cast_pow_specific : (↑(2 ^ 3) : ENNReal) = ↑2 ^ 3 := by
  ennreal_basic_simp

end TestSuite

end ENNRealArith
