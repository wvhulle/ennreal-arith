import ENNRealArith.Common
import ENNRealArith.Complex
import Qq

open Lean Meta Elab Tactic

namespace ENNRealArith


elab "ennreal_arith" : tactic  => do
  let tactics := [
    ← `(tactic| ennreal_mul_cancel),
    ← `(tactic| ennreal_fraction_add)
  ]
  for tac in tactics do
    if ← tryTactic tac then return

end ENNRealArith
