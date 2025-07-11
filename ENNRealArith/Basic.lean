import ENNRealArith.ArithmeticCore
import ENNRealArith.FractionOperations

open Lean Meta Elab Tactic ENNReal

namespace ENNRealArith

syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    let basicPattern? ← analyzeBasicArithmeticPattern target
    let invPattern? ← analyzeInversePattern target
    let hasMultInDiv ← analyzeMultiplicationInDivision target

    -- Handle case where no basic pattern is detected
    let some (hasAddition, hasMultiplication, hasDivision, _) := basicPattern? 
      | do evalTactic (← `(tactic| first
             | ennreal_basic_simp
             | ennreal_div_self
             | fail "ennreal_arith expects an equality goal"))

    -- Extract inverse information if available
    let hasInverse := invPattern?.map (·.1) |>.getD false

    -- Common pattern flags
    let isSimpleArithmetic := (hasAddition || hasMultiplication) && !hasDivision && !hasInverse
    let isConcrete ← isConcreteDivisionGoal target

    -- Determine which tactics to use based on patterns
    let tactics : TSyntax `tactic ←
      if isConcrete then
        `(tactic| first
          | ennreal_fraction_add
          | ennreal_div_self
          | ennreal_basic_simp
          | fail "ennreal_arith could not solve concrete division")
      else if hasInverse then
        `(tactic| first
          | ennreal_inv_transform
          | ennreal_fraction_add
          | ennreal_basic_simp
          | ennreal_div_self
          | fail "ennreal_arith could not solve inverse pattern")
      else if hasMultInDiv then
        `(tactic| first
          | ennreal_mul_div_assoc
          | ennreal_mul_cancel
          | ennreal_basic_simp
          | fail "ennreal_arith could not solve multiplication-division pattern")
      else if hasDivision then
        `(tactic| first
          | ennreal_div_self
          | ennreal_mul_cancel
          | ennreal_fraction_add
          | ennreal_basic_simp
          | fail "ennreal_arith could not solve division pattern")
      else if isSimpleArithmetic then
        `(tactic| first
          | ennreal_basic_simp
          | fail "ennreal_arith could not solve simple arithmetic")
      else
        `(tactic| first
          | ennreal_basic_simp
          | ennreal_div_self
          | ennreal_mul_cancel
          | ennreal_mul_div_assoc
          | ennreal_inv_transform
          | ennreal_fraction_add
          | fail "ennreal_arith could not solve the goal")

    evalTactic tactics


end ENNRealArith
