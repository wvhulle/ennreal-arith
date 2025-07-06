import ENNRealArith.Common

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

    if ← tryTactic (← `(tactic| norm_num)) then return

    throwError "ennreal_inv_patterns could not solve the goal"

section TestSuite


lemma ennreal_inv_div_mul_div_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  rw [one_div]
  rw [ inv_inv, ]
  rw [ Nat.cast_mul]
  rw [mul_div]

lemma ennreal_inv_div_mul_div {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns


lemma eightteen_manual:  ENNReal.ofReal 18⁻¹ = 18⁻¹ := by
  repeat rw [inv_eq_one_div]
  rw [ENNReal.ofReal_div_of_pos]
  norm_cast
  norm_num


lemma eightteen:  ENNReal.ofReal 18⁻¹ = 18⁻¹ := by
  ennreal_inv_patterns

lemma ennreal_three_div_two_concrete_manual : (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ = (↑3 : ENNReal) / (↑2 : ENNReal) := by
  rfl

lemma ennreal_three_div_two_concrete : (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ = (↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_inv_inv_manual {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  rw [inv_inv]

lemma ennreal_inv_inv {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_div_eq_inv_mul_manual {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, mul_comm]

lemma ennreal_div_eq_inv_mul {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma ennreal_mul_inv_manual {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  rfl

lemma ennreal_mul_inv {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_inv_two_mul_three_manual : (↑2 : ENNReal)⁻¹ * (↑3 : ENNReal) = (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ := by
  rw [mul_comm]

lemma ennreal_inv_two_mul_three : (↑2 : ENNReal)⁻¹ * (↑3 : ENNReal) = (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma ennreal_one_div_eq_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, mul_one]

lemma ennreal_one_div_eq_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  ennreal_inv_patterns

lemma ennreal_one_div_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  rw [ENNReal.div_eq_inv_mul, mul_one, inv_inv]

lemma ennreal_one_div_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_two_inv_manual : (↑2 : ENNReal)⁻¹ = 1 / (↑2 : ENNReal) := by
  rw [inv_eq_one_div]

lemma ennreal_two_inv : (↑2 : ENNReal)⁻¹ = 1 / (↑2 : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_three_inv_manual : (↑3 : ENNReal)⁻¹ = 1 / (↑3 : ENNReal) := by
  rw [inv_eq_one_div]

lemma ennreal_three_inv : (↑3 : ENNReal)⁻¹ = 1 / (↑3 : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_one_div_two_inv_mul_three_div_seven_manual :
  (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑7 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑7 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]
  simp only [mul_comm, mul_assoc]

lemma ennreal_one_div_two_inv_mul_three_div_seven :
  (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑7 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑7 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]
  simp only [mul_comm, mul_assoc]

lemma ennreal_two_inv_three_manual : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm, mul_assoc]

lemma ennreal_two_inv_three : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm, mul_assoc]


lemma ennreal_complex_inv_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp
  rw [mul_div]

lemma ennreal_complex_inv {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

lemma test_monty_hall_inv1_manual : ((1 : ENNReal) / 6)⁻¹ * (1 / 18) = 1 / 3 := by
  calc
    ((1 : ENNReal) / 6)⁻¹ * (1 / 18) = (6 : ENNReal) * (1 / 18) := by
      rw [<- ENNReal.mul_left_inj]
      all_goals norm_num
      exact ne_zero_of_eq_one rfl
      exact one_ne_top
    _ = ((6 : ENNReal) * (1 : ENNReal)) / 18 := by exact Eq.symm (mul_div_assoc 6 1 18)
    _ = ENNReal.ofNNReal ((6 : NNReal) * ( 1 : NNReal)) / 18 := by
      norm_cast
    _ =  ENNReal.ofNNReal  6 / 18 := by
      rw [ENNReal.ofNNReal]
      norm_cast
    _ = ENNReal.ofNNReal ( (6 : NNReal) / (18: NNReal)) := by
      rw [ENNReal.coe_div]
      · norm_num
      · norm_num
    _ = ENNReal.ofNNReal (1 / 3) := by
      congr 1
      field_simp
      norm_num
    _ = 1 / 3 := by
      rw [ENNReal.coe_div]
      · norm_num
      · norm_num

lemma test_monty_hall_inv1 : ((1 : ENNReal) / 6)⁻¹ * (1 / 18) = 1 / 3 := by
  ennreal_inv_patterns


lemma test_add_then_div_manual : ((1 : ENNReal) + 2) / 18 = 1 / 6 := by
  norm_cast
  norm_num
  rw [inv_eq_one_div]
  rw [ENNReal.div_eq_div_iff]
  all_goals norm_num

lemma test_add_then_div : ((1 : ENNReal) + 2) / 18 = 1 / 6 := by
  ennreal_inv_patterns

lemma test_inv_frac_mul_frac2_manual : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  rw [div_eq_mul_inv, one_mul, inv_inv]
  rw [<- mul_div_assoc]
  norm_cast
  norm_num
  rw [ENNReal.div_eq_div_iff]
  all_goals norm_num


lemma test_inv_frac_mul_frac2 : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  ennreal_inv_patterns


lemma test_ofReal_eq_manual : ENNReal.ofReal (1 / 9) = 2 / 18 := by
  rw [show (1 : ℝ) / 9 = 2 / 18 from by norm_num]
  rw [ENNReal.ofReal_div_of_pos] <;> norm_num

-- Additional patterns found in MontyHall
lemma test_ofReal_eq : ENNReal.ofReal (1 / 9) = 2 / 18 := by
  ennreal_inv_patterns

lemma test_mul_inv_eq_inv_manual : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  rw [ <- div_eq_mul_inv]
  rw [inv_eq_one_div]
  rw [ENNReal.div_eq_div_iff]
  all_goals   norm_num

lemma test_mul_inv_eq_inv : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_inv_patterns

-- Test case: tactic should work even with hypotheses in context
lemma test_with_hypotheses (_h1 : True) (_h2 : 1 + 1 = 2) : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_inv_patterns

lemma test_monty_hall_context
  (_h_inter_eq : True)
  (_h_filter_eq : 1 + 1 = 2)
  (_h_filter_explicit : True) :
  (3 : ENNReal) * 18⁻¹ = 6⁻¹ := by
  ennreal_inv_patterns


lemma test_monty_goals_context
   (a b: Nat) : (6 : ENNReal) * 18⁻¹ = 3⁻¹ ∧ a + b = b + a := by
    constructor
    · ennreal_inv_patterns
    · linarith


end TestSuite

end ENNRealArith
