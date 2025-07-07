import ENNRealArith.Common
import ENNRealArith.DivSelf

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for handling ENNReal inverse and division patterns.
Handles complex patterns involving inverses, divisions, and multiplications.
-/
syntax "ennreal_inv_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    let tactics : Array (TSyntax `tactic) := #[
      ← `(tactic| rfl),
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [mul_one]),
      ← `(tactic| rw [one_mul]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| (simp only [ mul_one, one_mul, inv_inv, mul_comm, mul_assoc])),
      ← `(tactic| simp only [mul_div, Nat.cast_mul]),
    ]


    -- Try multiplication-inverse equality pattern using sequence
    let mulInvEqInvTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [← div_eq_mul_inv, inv_eq_one_div]),
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence mulInvEqInvTactics then return



    let ofRealEarlyPattern : TacticM Bool := do
      try
        let goal ← getMainGoal
        goal.withContext do
          let target ← goal.getType

          match target with
          | .app (.app _ (.app (.const `ENNReal.ofReal _) _)) _ =>
            evalTactic (← `(tactic| repeat rw [inv_eq_one_div]))
            evalTactic (← `(tactic| rw [ENNReal.ofReal_div_of_pos] <;> norm_num))
            return (← getUnsolvedGoals).isEmpty
          | _ => return false
      catch _ => return false

    if ← ofRealEarlyPattern then return

    for tac in tactics do
      if ← tryTactic tac then return



    -- Try division equality pattern using sequence
    let divEqDivTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence divEqDivTactics then return


    if ← tryTactic (← `(tactic| (norm_cast; ennreal_div_self))) then return

    -- Try multiplication division cancellation pattern using sequence
    let mulDivCancelTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)])
    ]
    if ← tryTacticSequence mulDivCancelTactics then return

    let invMulToDivPattern : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [mul_comm]))
        evalTactic (← `(tactic| rw [← div_eq_mul_inv]))
        evalTactic (← `(tactic| all_goals (first | assumption | apply_assumption | simp [ne_eq])))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    if ← invMulToDivPattern then return

    evalTactic (← `(tactic| all_goals assumption))

section TestSuite

lemma test_inverse_multiplication_to_division {a b : ℕ} (ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by
    ennreal_inv_patterns




example: 1 / 2 * (1 / 3) / 2⁻¹ = (3⁻¹ : ENNReal) := by
  ennreal_inv_patterns



lemma un_simplify_fraction : (1: ENNReal) / 9 = 2 / 18 := by
  ennreal_inv_patterns

lemma mul_simplify : ((1 :ENNReal)/6)⁻¹ * (2/18) = 2/3 := by
  ennreal_inv_patterns


lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns


lemma test_ofReal_inverse_equality:  ENNReal.ofReal 18⁻¹ = 18⁻¹ := by
  ennreal_inv_patterns

lemma test_multiplication_by_inverse_equals_division : (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ = (↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_inv_patterns

lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

lemma test_division_as_inverse_multiplication {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma test_inverse_multiplication_as_division {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_inv_patterns

lemma test_inverse_multiplication_commutativity : (↑2 : ENNReal)⁻¹ * (↑3 : ENNReal) = (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma test_reciprocal_of_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

lemma test_inverse_as_reciprocal_two : (↑2 : ENNReal)⁻¹ = 1 / (↑2 : ENNReal) := by
  ennreal_inv_patterns

lemma test_inverse_as_reciprocal_three : (↑3 : ENNReal)⁻¹ = 1 / (↑3 : ENNReal) := by
  ennreal_inv_patterns

lemma test_complex_inverse_fraction_pattern_2_3_7 :
  (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑7 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑7 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]
  simp only [mul_comm, mul_assoc]

lemma test_complex_inverse_fraction_pattern_2_3_5 : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm, mul_assoc]


lemma test_inverse_fraction_multiplication_generic {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

lemma test_inverse_fraction_concrete_6_18_3 : ((1 : ENNReal) / 6)⁻¹ * (1 / 18) = 1 / 3 := by
  ennreal_inv_patterns



lemma test_inverse_fraction_multiplication_6_18 : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  ennreal_inv_patterns


lemma test_ofReal_fraction_equality : ENNReal.ofReal (1 / 9) = 2 / 18 := by
  ennreal_inv_patterns

lemma test_multiplication_inverse_equals_inverse : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_inv_patterns



end TestSuite

end ENNRealArith
