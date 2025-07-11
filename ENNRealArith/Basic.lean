import ENNRealArith.Common
import ENNRealArith.Complex
import Qq

open Lean Meta Elab Tactic

namespace ENNRealArith


elab "ennreal_arith" : tactic => do
  evalTactic (← `(tactic|
    first
    | (ennreal_mul_cancel; done)
    | (ennreal_fraction_add; done)
    ))

end ENNRealArith
