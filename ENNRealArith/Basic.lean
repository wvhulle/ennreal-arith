import ENNRealArith.ArithmeticCore
import ENNRealArith.FractionOperations

open Lean Meta Elab Tactic ENNReal

namespace ENNRealArith

syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget


    if ← isConcreteDivisionGoal target then
      if ← tryTactic (← `(tactic| ennreal_fraction_add)) then return

    let fallbackTactics := [
      ← `(tactic| ennreal_mul_cancel),
      ← `(tactic| ennreal_fraction_add),
    ]

    for tac in fallbackTactics do
      if ← tryTactic tac then return

    throwError "ennreal_arith could not solve the goal"


end ENNRealArith
