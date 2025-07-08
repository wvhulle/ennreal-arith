import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

import ENNRealArith.Common
import ENNRealArith.ArithmeticCore

set_option linter.docPrime false

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith


syntax "ennreal_mul_div_assoc" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    let patterns? ← analyzeEqualityGoal target

    match patterns? with
    | some (lhs, rhs) =>
      let hasMultInDiv := lhs.hasMultiplicationInDivision || rhs.hasMultiplicationInDivision
      let hasSimpleArith := lhs.isSimpleArithmetic || rhs.isSimpleArithmetic

      if hasMultInDiv then
        if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return
      else if hasSimpleArith then
        if ← tryTactic (← `(tactic| norm_num)) then return
        if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, Nat.cast_mul])) then return

      if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return

      if ← tryTacticSequence [
        ← `(tactic| apply ENNReal.div_self),
        ← `(tactic| apply Nat.cast_ne_zero.mpr),
        ← `(tactic| assumption),
        ← `(tactic| exact ENNReal.coe_ne_top)
      ] then return

    | none =>
      throwError "ennreal_mul_div_assoc expects an equality goal"

    throwError "ennreal_mul_div_assoc could not solve the goal"


syntax "ennreal_inv_transform" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryTactic (← `(tactic| rfl)) then return

    let patterns? ← analyzeEqualityGoal target

    match patterns? with
    | some (lhs, rhs) =>
      let hasDoubleInv := lhs.hasDoubleInverse || rhs.hasDoubleInverse
      let hasInverse := lhs.hasInverse || rhs.hasInverse
      let hasDivision := lhs.hasDivision || rhs.hasDivision
      let hasInvMulDiv := lhs.hasMultiplicationInDivision || rhs.hasMultiplicationInDivision

      if hasDoubleInv then
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, one_div])) then return

      if hasInverse && hasDivision then
        if ← tryTactic (← `(tactic| simp only [div_eq_mul_inv, mul_comm])) then return

      if hasInverse && !hasDivision then
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul])) then return

      if hasInvMulDiv then
        if ← tryTacticSequence [
          ← `(tactic| simp only [one_div, inv_inv]),
          ← `(tactic| ennreal_mul_div_assoc)
        ] then return

      if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                             div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul])) then return

    | none =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div])) then return
    let remainingTactics := [
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| simp only [mul_div, Nat.cast_mul])
    ]

    for tac in remainingTactics do
      if ← tryTactic tac then return

    if ← tryTacticSequence [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ] then return

    evalTactic (← `(tactic| all_goals assumption))

/-- Convert an ENNReal equation to a Real equation when both sides are not infinity -/
lemma ennreal_eq_via_toReal {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]

syntax "ennreal_fraction_add" : tactic

elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget
    
    if ← tryTactic (← `(tactic| norm_num)) then return

    let patterns? ← analyzeEqualityGoal target
    
    if isConcreteDivisionGoal target then
      if ← tryTactic (← `(tactic| ennreal_div_self)) then return
    match patterns? with
    | some (lhs, rhs) =>
      let hasInverse := lhs.hasInverse || rhs.hasInverse
      let hasAddition := lhs.hasAddition || rhs.hasAddition
      let isSimpleArithmetic := lhs.isSimpleArithmetic && rhs.isSimpleArithmetic
      
      if isSimpleArithmetic then
        if ← tryTactic (← `(tactic| simp only [add_zero, zero_add, mul_one, one_mul])) then return
      
      if hasInverse then
        let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))
        let _ ← tryTactic (← `(tactic| ennreal_inv_transform))
        if hasAddition then
          let _ ← tryTactic (← `(tactic| norm_num1))
      else if hasAddition then
        let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add]))
      
    | none =>
      let _ ← tryTactic (← `(tactic| simp only [add_zero, zero_add]))
    
    let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))

    repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

    let _ ← tryTactic (← `(tactic| ennreal_inv_transform))

    if ← tryTactic (← `(tactic| ennreal_div_self)) then return

    if (← getUnsolvedGoals).isEmpty then return

    if ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num)
    ] then return

    if ← tryTacticSequence [
      ← `(tactic| simp only [inv_eq_one_div]),
      ← `(tactic| rw [← ENNReal.add_div]),
      ← `(tactic| norm_num)
    ] then return
    
    throwError "ennreal_fraction_add could not solve the goal"



section MulDivAssocTests


lemma test_mul_div_associativity_right {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_left {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_concrete : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_preserves_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_div_mul_associativity {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

end MulDivAssocTests

section InvPatternTests

lemma test_inverse_multiplication_to_division {a b : ℕ} (_ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform

lemma test_division_as_inverse_multiplication {a b : ℕ} :
  (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform

lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  simp only [inv_inv]

lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  simp only [inv_eq_one_div]

lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp only [one_div, inv_inv, mul_div]

end InvPatternTests

section FractionAddTests

lemma test_nested_addition_division :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_fraction_add



lemma test_addition_then_division : ((1 : ENNReal) + 2) / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 3 / 18 := by
  ennreal_fraction_add

lemma test_basic_arithmetic : (2 : ENNReal) + 3 = 5 := by
  ennreal_fraction_add

lemma test_zero_addition : (1 : ENNReal) / 6 + 0 = 1 / 6 := by
  ennreal_fraction_add

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by
  ennreal_fraction_add



end FractionAddTests

end ENNRealArith
