import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Qq

import ENNRealArith.Common
import ENNRealArith.Simple

set_option linter.docPrime false

open Lean Meta Elab Tactic
open ENNReal Qq

namespace ENNRealArith



/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/
elab "ennreal_mul_cancel" : tactic => do
  let goal ← getMainGoal
  goal.withContext do

    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero,
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    let attemptCancellation : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      catch _ => pure ()

      let tryMulDiv (tac : TSyntax `tactic) : TacticM Bool := do
        try
          evalTactic tac
          evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
          evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
          tryNonzeroProof
          evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
          return (← getUnsolvedGoals).isEmpty
        catch _ => return false

      if ← tryMulDiv (← `(tactic| apply ENNReal.mul_div_mul_right)) then return true
      if ← tryMulDiv (← `(tactic| apply ENNReal.mul_div_mul_left)) then return true
      return false

    if ← attemptCancellation then return




elab "ennreal_fraction_add" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryTactic (← `(tactic| norm_num)) then return

    if ← isConcreteDivisionGoal target then
      if ← tryTactic (← `(tactic| ennreal_div_self)) then return

    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q(($num1 : ENNReal) / $denom + ($num2 : ENNReal) / $denom2 = ($res : ENNReal) / $denom3) =>
      if (← isDefEq denom denom2) && (← isDefEq denom denom3) then
      if ← tryTactic (← `(tactic| rw [← ENNReal.add_div])) then return
      if ← tryTactic (← `(tactic| norm_num)) then return

    | ~q(($lhs : ENNReal) + $rhs = $sum) =>
      if ← tryTactic (← `(tactic| simp only [add_zero, zero_add])) then return
      if ← tryTactic (← `(tactic| norm_num)) then return

    | _ => pure ()

    let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))

    repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

    let _ ← tryTactic (← `(tactic| ennreal_inv_transform))

    if (← getUnsolvedGoals).isEmpty then return

    if ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num)
    ] then return
