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

    let some (_, _, _, _) := basicPattern?
      | do evalTactic (← `(tactic| first
             | ennreal_basic_simp
             | ennreal_div_self
             | fail "ennreal_arith expects an equality goal"))

    let isConcrete ← isConcreteDivisionGoal target

    let primaryTactic : TSyntax `tactic ←
      if isConcrete then
        `(tactic| ennreal_fraction_add)
      else
        `(tactic| ennreal_basic_simp)

    try
      evalTactic primaryTactic
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    let fallbackTactics ← `(tactic| first
      | ennreal_mul_cancel
      | ennreal_inv_transform)

    evalTactic fallbackTactics


end ENNRealArith
