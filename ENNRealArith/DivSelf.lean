import ENNRealArith.Common

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`.
-/
syntax "ennreal_div_self" : tactic

elab_rules : tactic | `(tactic| ennreal_div_self) => do
  try
    evalTactic (← `(tactic| apply ENNReal.div_self))
    evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
    evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
    tryNonzeroProof
    evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    if (← getUnsolvedGoals).isEmpty then return
  catch _ => pure ()

  throwError "ennreal_div_self could not solve the goal"



section TestSuite

-- Core division by self functionality
lemma test_division_self_nonzero {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_div_self
lemma test_division_self_successor {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_div_self

-- Concrete examples
lemma test_division_self_concrete : (↑2 : ENNReal) / ↑2 = 1 := by ennreal_div_self

end TestSuite

end ENNRealArith

#lint
