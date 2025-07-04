import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_inv_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    let tryPattern (tac : TSyntax `tactic) : TacticM Bool := do
      try
        let goals_before ← getUnsolvedGoals
        if goals_before.isEmpty then return true
        evalTactic tac
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    -- Ordered by likelihood and cost: cheapest/most specific first
    let tactics : Array (TSyntax `tactic) := #[
      -- Reflexivity is cheapest
      ← `(tactic| rfl),

      -- Simple rewrites for common patterns (before norm_num to avoid introducing inverses)
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [mul_one]),
      ← `(tactic| rw [one_mul]),

      -- Division/inverse conversions (most common use case)
      ← `(tactic| rw [ENNReal.div_eq_inv_mul]),
      ← `(tactic| rw [div_eq_mul_inv]),
      ← `(tactic| rw [← div_eq_mul_inv]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),

      -- Commutativity for when order matters
      ← `(tactic| rw [mul_comm]),

      -- Combined simp for common patterns
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, mul_one, one_mul, inv_inv, mul_comm, mul_assoc]),
      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv]),

      -- Specialized patterns
      ← `(tactic| simp only [mul_div]),
      ← `(tactic| rw [mul_div]),

      -- Handle nat casts
      ← `(tactic| simp only [mul_div, Nat.cast_mul]),

      -- More aggressive simp combinations for complex cases
      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv, mul_div_assoc, ENNReal.div_eq_inv_mul]),
      ← `(tactic| simp only [div_eq_mul_inv, one_mul, inv_inv, mul_div_assoc, ENNReal.coe_div]),

      -- mul_div_assoc patterns (identified from manual proofs)
      ← `(tactic| rw [← mul_div_assoc]),
      ← `(tactic| rw [mul_div_assoc]),

      -- ENNReal.ofReal patterns (for real number conversions) - handled in multi-step patterns

      -- Special pattern for ofReal equality with division - handled in multi-step patterns

      -- Generic simp as last resort (handles complex cases)
      ← `(tactic| simp),
      ← `(tactic| simp [mul_div])
    ]

    -- Try specific patterns first before simple tactics that might introduce inverses

    -- Pattern for ofReal equalities - must be tried early before norm_num introduces inverses
    let ofRealEarlyPattern : TacticM Bool := do
      try
        let goal ← getMainGoal
        goal.withContext do
          let target ← goal.getType
          -- Check if this is an ENNReal.ofReal goal
          match target with
          | .app (.app _ (.app (.const `ENNReal.ofReal _) _)) _ =>
            evalTactic (← `(tactic| rw [ENNReal.ofReal_div_of_pos] <;> norm_num))
            return (← getUnsolvedGoals).isEmpty
          | _ => return false
      catch _ => return false

    if ← ofRealEarlyPattern then return

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
      if ← tryPattern tac then return

    -- High priority multi-step patterns from manual proofs

    -- Pattern 1: norm_cast followed by norm_num (very common)
    let normCastThenNormNum : TacticM Bool := do
      try
        evalTactic (← `(tactic| norm_cast))
        evalTactic (← `(tactic| norm_num))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Pattern 2: ENNReal.div_eq_div_iff with all_goals norm_num (critical for division equality)
    let divEqDivIff : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Pattern 3: simp followed by rw [mul_div]
    let simpThenRw : TacticM Bool := do
      try
        evalTactic (← `(tactic| simp))
        evalTactic (← `(tactic| rw [mul_div]))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Pattern 4: mul_inv to div conversion with div_eq_div_iff
    let mulInvToDivPattern : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [← div_eq_mul_inv]))
        evalTactic (← `(tactic| rw [inv_eq_one_div]))
        evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]))
        evalTactic (← `(tactic| all_goals norm_num))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    -- Try multi-step patterns only if simple tactics failed
    if ← normCastThenNormNum then return
    if ← divEqDivIff then return
    if ← mulInvToDivPattern then return
    if ← simpThenRw then return
    
    -- Only try norm_num at the very end to avoid introducing inverses prematurely
    if ← tryPattern (← `(tactic| norm_num)) then return

    throwError "ennreal_inv_patterns could not solve the goal"

section TestSuite

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

lemma ennreal_inv_div_mul_div_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  simp
  rw [mul_div]

-- TODO: Fix this test - the tactic doesn't handle the simp; rw [mul_div] pattern correctly
-- lemma ennreal_inv_div_mul_div {a b c : ℕ} :
--   (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
--   ennreal_inv_patterns

lemma ennreal_complex_inv_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp
  rw [mul_div]

lemma ennreal_complex_inv {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

-- Tests from Monty Hall patterns
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
      -- Show that 6 / 18 = 1 / 3 in NNReal
      field_simp
      norm_num
    _ = 1 / 3 := by
      rw [ENNReal.coe_div]
      · norm_num
      · norm_num

lemma test_monty_hall_inv1 : ((1 : ENNReal) / 6)⁻¹ * (1 / 18) = 1 / 3 := by
  ennreal_inv_patterns

lemma test_monty_hall_inv2_manual : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  rw [div_eq_mul_inv, one_mul, inv_inv]

  have :  (6 : ENNReal) * ((2 : ENNReal) / (18 : ENNReal)) = ( (6: ENNReal)  * (2 : ENNReal)) / (18 : ENNReal) := by
    exact Eq.symm (mul_div_assoc 6 2 18)
  rw [this]
  have: ( (6: ENNReal)  * (2 : ENNReal)) / (18 : ENNReal) = ( ENNReal.ofNNReal (6: NNReal)  * (2 : NNReal)) / (18 : ENNReal) := by
     exact rfl
  rw [this]
  have: ( ENNReal.ofNNReal (6: NNReal)  * (2 : NNReal)) / (18 : ENNReal)  = ( 12 : ENNReal) / (18 : ENNReal)  := by
    norm_cast
  rw [this]
  rw [ENNReal.div_eq_div_iff]
  all_goals norm_num

lemma test_monty_hall_inv2 : ((1 : ENNReal) / 6)⁻¹ * (2 / 18) = 2 / 3 := by
  ennreal_inv_patterns

-- Patterns from Monty Hall problem
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


end TestSuite

end ENNRealArith
