import ENNRealArith.BasicSimp
import ENNRealArith.DivSelf
import ENNRealArith.MulCancel
import ENNRealArith.MulDivAssoc
import ENNRealArith.InvPatterns

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let goal ← getMainGoal
  goal.withContext do
    let tactics := [
      `(tactic| ennreal_basic_simp),
      `(tactic| ennreal_div_self),
      `(tactic| ennreal_mul_cancel),
      `(tactic| ennreal_mul_div_assoc),
      `(tactic| ennreal_inv_patterns)
    ]

    for tac in tactics do
      try
        evalTactic (← tac)
        if (← getUnsolvedGoals).isEmpty then return
      catch _ => continue

    throwError "ennreal_arith could not solve the goal"


section ComplexArithmeticTests

lemma test_basic_add : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_basic_add_mul : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_basic_zero_one {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

lemma test_add_zero_mul_one {a b : ℕ} : (↑a : ENNReal) + 0 * ↑b = ↑a := by ennreal_arith

lemma test_zero_mul {a b : ℕ} : 0 * (↑a : ENNReal) + ↑b = ↑b := by ennreal_arith

lemma test_div_self_basic {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

lemma test_div_self_succ (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_arith

lemma test_div_self_concrete : (↑5 : ENNReal) / ↑5 = 1 := by ennreal_arith

lemma test_mul_cancel_basic {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith

lemma test_mul_cancel_concrete :
  (↑(2 * 3) : ENNReal) / (↑(4 * 3)) = (↑2) / (↑4) := by ennreal_arith

lemma test_mul_cancel_left {a b c : ℕ} (hc : c ≠ 0) :
  (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by ennreal_arith

lemma test_mul_div_assoc_basic {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_arith

lemma test_mul_div_assoc_concrete :
  (↑3 : ENNReal) * ((↑4 : ENNReal) / (↑5 : ENNReal)) = (↑12 : ENNReal) / (↑5 : ENNReal) := by ennreal_arith

lemma test_mul_div_assoc_right {a b c : ℕ} :
  ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_arith

lemma test_inv_mul_basic {a b : ℕ} :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_arith

lemma test_inv_div_basic {a b : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * (↑b : ENNReal) = (↑(a * b) : ENNReal) := by ennreal_arith

lemma test_inv_concrete :
  (↑3 : ENNReal)⁻¹ * (↑6 : ENNReal) = (↑6 : ENNReal) / (↑3 : ENNReal) := by ennreal_arith

lemma test_complex_basic :
  (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

lemma test_large_basic_expression :
  (↑1 : ENNReal) + ↑2 * ↑3 + ↑4 * 1 + 0 * ↑5 = ↑11 := by ennreal_arith

lemma test_nested_mul_div {a b c d : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) * ((↑c : ENNReal) / (↑d : ENNReal))) =
  (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by ennreal_arith

end ComplexArithmeticTests

end ENNRealArith
