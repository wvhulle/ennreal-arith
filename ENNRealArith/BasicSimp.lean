import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  let goal ← getMainGoal
  goal.withContext do
    let tryTactics (tactics : List (TSyntax `tactic)) : TacticM Bool := do
      try
        for tac in tactics do evalTactic tac
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    let tacticSequences := [
      [← `(tactic| norm_num)],
      [← `(tactic| norm_cast)],
      [← `(tactic| simp)],
      [← `(tactic| norm_cast), ← `(tactic| norm_num)],
      -- Handle fraction addition and inverse patterns
      [← `(tactic| simp only [add_zero, zero_add, inv_eq_one_div])],
      [← `(tactic| simp only [add_zero, zero_add]), ← `(tactic| norm_num)],
      [← `(tactic| rw [ENNReal.div_eq_div_iff]), ← `(tactic| all_goals norm_num)]
    ]

    for sequence in tacticSequences do
      if ← tryTactics sequence then return

    throwError "ennreal_basic_simp could not solve the goal"

section TestSuite

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



lemma ennreal_add_zero_manual {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by
  simp only [add_zero]

lemma ennreal_add_zero {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by
  ennreal_basic_simp

lemma ennreal_mul_one_manual {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by
  simp only [mul_one]

lemma ennreal_mul_one {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by
  ennreal_basic_simp

lemma ennreal_mul_zero_manual {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by
  simp only [mul_zero]

lemma ennreal_mul_zero {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by
  ennreal_basic_simp

lemma ennreal_div_one_manual {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by
  simp only [div_one]

lemma ennreal_div_one {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by
  ennreal_basic_simp

lemma ennreal_zero_div_manual {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by
  simp only [ENNReal.zero_div]

lemma ennreal_zero_div {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by
  ennreal_basic_simp



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

lemma ennreal_sub_five_three_manual : (↑5 : ENNReal) - ↑3 = ↑2 := by
  norm_cast

lemma ennreal_sub_five_three : (↑5 : ENNReal) - ↑3 = ↑2 := by
  ennreal_basic_simp



lemma ennreal_add_cast_manual {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by
  norm_cast

lemma ennreal_add_cast {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by
  ennreal_basic_simp

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

end TestSuite

end ENNRealArith
