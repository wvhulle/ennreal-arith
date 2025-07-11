import ENNRealArith.ArithmeticCore
import ENNRealArith.FractionOperations
import Qq

open Lean Meta Elab Tactic ENNReal Qq

namespace ENNRealArith

syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let goal ← getMainGoal
  goal.withContext do
    let fallbackTactics := [
      ← `(tactic| ennreal_mul_cancel),
      ← `(tactic| ennreal_fraction_add),
    ]

    for tac in fallbackTactics do
      if ← tryTactic tac then return



end ENNRealArith
