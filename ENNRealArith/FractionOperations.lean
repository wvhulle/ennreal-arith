import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Qq

import ENNRealArith.Common
import ENNRealArith.ArithmeticCore

set_option linter.docPrime false

open Lean Meta Elab Tactic
open ENNReal Qq

namespace ENNRealArith

elab "ennreal_mul_div_assoc": tactic  => do
  let goal ← getMainGoal
  goal.withContext do
    let mainTactics := [
      ← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul]),
      ← `(tactic| norm_num),
      ← `(tactic| simp only [mul_one, one_mul, Nat.cast_mul])
    ]

    for tac in mainTactics do
      if ← tryTactic tac then return

    if ← tryTacticSequence [
      ← `(tactic| apply ENNReal.div_self),
      ← `(tactic| apply Nat.cast_ne_zero.mpr),
      ← `(tactic| assumption),
      ← `(tactic| exact ENNReal.coe_ne_top)
    ] then return

    throwError "ennreal_mul_div_assoc could not solve the goal"


elab "ennreal_inv_transform" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryTactic (← `(tactic| rfl)) then return

    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q((($a : ENNReal)⁻¹)⁻¹ = $b) =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, one_div])) then return

    | ~q((($a : ENNReal)⁻¹) / $b = $c) =>
      if ← tryTactic (← `(tactic| simp only [div_eq_mul_inv, mul_comm, inv_eq_one_div])) then return

    | ~q((($a : ENNReal)⁻¹) * $b = $c) =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul, mul_comm])) then return
      if ← tryTactic (← `(tactic| rw [← div_eq_mul_inv])) then return

    | ~q(($a : ENNReal) * (($b : ENNReal)⁻¹) = $c) =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul, mul_comm])) then return
      if ← tryTactic (← `(tactic| rw [← div_eq_mul_inv])) then return

    | ~q(($a : ENNReal) / $b * $c = $d) =>
      if ← tryTacticSequence [
        ← `(tactic| simp only [one_div, inv_inv]),
        ← `(tactic| ennreal_mul_div_assoc)
      ] then return

    | _ =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div])) then return

    if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                           div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul, one_div])) then return

    let remainingTactics := [
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| simp only [mul_div, Nat.cast_mul])
    ]

    for tac in remainingTactics do
      if ← tryTactic tac then return

    if ← tryTacticSequence [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ] then return

    evalTactic (← `(tactic| all_goals assumption))


/-- Convert an ENNReal equation to a Real equation when both sides are not infinity -/
lemma ennreal_eq_via_toReal {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]


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


    throwError "ennreal_fraction_add could not solve the goal"

end ENNRealArith
