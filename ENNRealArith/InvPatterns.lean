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


      ← `(tactic| rw [ENNReal.div_eq_inv_mul]),
      ← `(tactic| rw [div_eq_mul_inv]),
      ← `(tactic| rw [← div_eq_mul_inv]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),


      ← `(tactic| rw [mul_comm]),


      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, mul_one, one_mul, inv_inv, mul_comm, mul_assoc]),
      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv]),


      ← `(tactic| simp only [mul_div]),
      ← `(tactic| rw [mul_div]),


      ← `(tactic| simp only [mul_div, Nat.cast_mul]),


      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv, mul_div_assoc, ENNReal.div_eq_inv_mul]),
      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv, mul_div_assoc, ENNReal.coe_div]),


      ← `(tactic| rw [← mul_div_assoc]),
      ← `(tactic| rw [mul_div_assoc]),




      ← `(tactic| simp),
      ← `(tactic| simp [mul_div])
    ]



    let mulInvEqInvPattern : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [← div_eq_mul_inv, inv_eq_one_div]))
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    if ← mulInvEqInvPattern then return

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

    -- Pattern for: (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal)
    let invFracMulFracPatternEarly_alt : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [one_div, inv_inv, Nat.cast_mul, mul_div]))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false


    if ← invFracMulFracPatternEarly_alt then return

    -- Pattern for: ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3
    let invFracMulFracPatternEarly : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]))
        evalTactic (← `(tactic| rw [← mul_div_assoc]))
        evalTactic (← `(tactic| norm_cast))
        evalTactic (← `(tactic| norm_num))
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    if ← invFracMulFracPatternEarly then return

    for tac in tactics do
      if ← tryTactic tac then return


    let divEqDivIff : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    let simpThenRw : TacticM Bool := do
      try
        evalTactic (← `(tactic| simp only [ENNReal.div_eq_inv_mul, mul_one, one_mul, inv_inv]))
        evalTactic (← `(tactic| rw [mul_div]))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    let generalSimpThenRw : TacticM Bool := do
      try
        evalTactic (← `(tactic| simp))
        evalTactic (← `(tactic| rw [mul_div]))
        let remainingGoals ← getUnsolvedGoals
        if !remainingGoals.isEmpty then
          evalTactic (← `(tactic| simp [mul_comm, mul_assoc, mul_left_comm]))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    let mulInvToDivPattern : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [← div_eq_mul_inv]))
        evalTactic (← `(tactic| rw [inv_eq_one_div]))
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    if ← divEqDivIff then return
    if ← mulInvToDivPattern then return
    if ← simpThenRw then return
    if ← generalSimpThenRw then return

    -- Pattern for a / a = 1 (like 18 / 18 = 1)
    if ← tryTactic (← `(tactic| ennreal_div_self)) then return
    
    -- Pattern for numeric literals like 18 / 18 = 1
    if ← tryTactic (← `(tactic| (norm_cast; ennreal_div_self))) then return

    if ← tryTactic (← `(tactic| norm_num)) then return

    throwError "ennreal_inv_patterns could not solve the goal"

section TestSuite

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


lemma test_addition_then_division : ((1 : ENNReal) + 2) / 18 = 1 / 6 := by
  ennreal_inv_patterns

lemma test_inverse_fraction_multiplication_6_18 : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  ennreal_inv_patterns


lemma test_ofReal_fraction_equality : ENNReal.ofReal (1 / 9) = 2 / 18 := by
  ennreal_inv_patterns

lemma test_multiplication_inverse_equals_inverse : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_inv_patterns

lemma test_inverse_pattern_with_context (_h1 : True) (_h2 : 1 + 1 = 2) : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_inv_patterns

lemma test_inverse_pattern_multiple_hypotheses
  (_h_inter_eq : True)
  (_h_filter_eq : 1 + 1 = 2)
  (_h_filter_explicit : True) :
  (3 : ENNReal) * 18⁻¹ = 6⁻¹ := by
  ennreal_inv_patterns


lemma test_inverse_pattern_with_conjunction
   (a b: Nat) : (6 : ENNReal) * 18⁻¹ = 3⁻¹ ∧ a + b = b + a := by
    constructor
    · ennreal_inv_patterns
    · linarith


end TestSuite

end ENNRealArith
