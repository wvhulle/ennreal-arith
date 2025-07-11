import ENNRealArith.FractionOperations
import Qq

open Lean ENNRealArith


elab "ennreal_arith" : tactic  => do
  let tactics := [
    ← `(tactic| ennreal_mul_cancel),
    ← `(tactic| ennreal_fraction_add)
  ]
  for tac in tactics do
    if ← tryTactic tac then return
