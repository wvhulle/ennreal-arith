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
    let some (_, _, hasDivision, _) := basicPattern?
      | do evalTactic (← `(tactic| first
             | ennreal_basic_simp
             | ennreal_div_self
             | fail "ennreal_arith expects an equality goal"))

    -- Extract pattern information
    let hasInverse := invPattern?.map (·.1) |>.getD false
    let isConcrete ← isConcreteDivisionGoal target

    -- Determine primary tactic based on pattern priority
    let primaryTactic : TSyntax `tactic ←
      if isConcrete then
        `(tactic| ennreal_fraction_add)
      else if hasInverse then
        `(tactic| ennreal_inv_transform)
      else if hasMultInDiv then
        `(tactic| ennreal_mul_div_assoc)
      else if hasDivision then
        `(tactic| ennreal_div_self)
      else
        `(tactic| ennreal_basic_simp)

    -- Execute primary tactic first, then fallbacks
    try
      evalTactic primaryTactic
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Build comprehensive fallback list (order matters for efficiency)
    let fallbackTactics ← `(tactic| first
      | ennreal_basic_simp
      | ennreal_div_self
      | ennreal_mul_cancel
      | ennreal_fraction_add
      | ennreal_mul_div_assoc
      | ennreal_inv_transform
      | fail "ennreal_arith could not solve the goal")

    evalTactic fallbackTactics


end ENNRealArith
