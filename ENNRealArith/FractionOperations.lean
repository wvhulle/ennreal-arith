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

/--
Analyzes inverse patterns using QQ pattern matching.
Returns booleans for: hasInverse, hasDoubleInverse, hasInverseWithDivision, hasInverseWithMultiplication
-/
def analyzeInversePattern (target : Expr) : MetaM (Option (Bool × Bool × Bool × Bool)) := do
  -- Check that we have a Prop goal
  let targetType ← inferType target
  unless ← isDefEq targetType q(Prop) do
    return none

  -- Use QQ pattern matching on the target
  have targetQ : Q(Prop) := target
  match targetQ with

  -- Double inverse patterns: a⁻¹⁻¹ = b
  | ~q((($a : ENNReal)⁻¹)⁻¹ = $b) => return some (true, true, false, false)
  | ~q(($a : ENNReal) = (($b)⁻¹)⁻¹) => return some (true, true, false, false)

  -- Inverse with division: a⁻¹ / b = c or a / b⁻¹ = c
  | ~q((($a : ENNReal)⁻¹) / $b = $c) => return some (true, false, true, false)
  | ~q(($a : ENNReal) / (($b)⁻¹) = $c) => return some (true, false, true, false)
  | ~q(($a : ENNReal) = (($b)⁻¹) / $c) => return some (true, false, true, false)
  | ~q(($a : ENNReal) = $b / (($c)⁻¹)) => return some (true, false, true, false)

  -- Inverse with multiplication: a⁻¹ * b = c or a * b⁻¹ = c
  | ~q((($a : ENNReal)⁻¹) * $b = $c) => return some (true, false, false, true)
  | ~q(($a : ENNReal) * (($b)⁻¹) = $c) => return some (true, false, false, true)
  | ~q(($a : ENNReal) = (($b)⁻¹) * $c) => return some (true, false, false, true)
  | ~q(($a : ENNReal) = $b * (($c)⁻¹)) => return some (true, false, false, true)

  -- Inverse with both division and multiplication: a⁻¹ * b / c = d
  | ~q((($a : ENNReal)⁻¹) * $b / $c = $d) => return some (true, false, true, true)
  | ~q(($a : ENNReal) * (($b)⁻¹) / $c = $d) => return some (true, false, true, true)
  | ~q(($a : ENNReal) / $b * (($c)⁻¹) = $d) => return some (true, false, true, true)
  | ~q(($a : ENNReal) = (($b)⁻¹) * $c / $d) => return some (true, false, true, true)
  | ~q(($a : ENNReal) = $b * (($c)⁻¹) / $d) => return some (true, false, true, true)
  | ~q(($a : ENNReal) = $b / $c * (($d)⁻¹)) => return some (true, false, true, true)

  -- Simple inverse patterns: a⁻¹ = b
  | ~q((($a : ENNReal)⁻¹) = $b) => return some (true, false, false, false)
  | ~q(($a : ENNReal) = (($b)⁻¹)) => return some (true, false, false, false)

  -- Complex patterns with addition and inverse
  | ~q((($a : ENNReal)⁻¹) + $b = $c) => return some (true, false, false, false)
  | ~q(($a : ENNReal) + (($b)⁻¹) = $c) => return some (true, false, false, false)
  | ~q(($a : ENNReal) = (($b)⁻¹) + $c) => return some (true, false, false, false)
  | ~q(($a : ENNReal) = $b + (($c)⁻¹)) => return some (true, false, false, false)

  | _ => return none

/--
Detects multiplication in division patterns using QQ pattern matching.
Returns whether the expression contains multiplication with division.
-/
def analyzeMultiplicationInDivision (target : Expr) : MetaM Bool := do
  -- Check that we have a Prop goal
  let targetType ← inferType target
  unless ← isDefEq targetType q(Prop) do
    return false

  -- Use QQ pattern matching on the target
  have targetQ : Q(Prop) := target
  match targetQ with

  -- Patterns with multiplication and division: (a * (b / c)) = d or (a / b) * c = d
  | ~q(($a : ENNReal) * ($b / $c) = $d) => return true
  | ~q(($a / $b : ENNReal) * $c = $d) => return true
  | ~q(($a : ENNReal) = $b * ($c / $d)) => return true
  | ~q(($a : ENNReal) = ($b / $c) * $d) => return true

  -- More complex patterns with nat casts
  | ~q((↑$na : ENNReal) * ((↑$nb : ENNReal) / (↑$nc : ENNReal)) = $d) => return true
  | ~q(((↑$na : ENNReal) / (↑$nb : ENNReal)) * (↑$nc : ENNReal) = $d) => return true
  | ~q(($a : ENNReal) = (↑$nb : ENNReal) * ((↑$nc : ENNReal) / (↑$nd : ENNReal))) => return true
  | ~q(($a : ENNReal) = ((↑$nb : ENNReal) / (↑$nc : ENNReal)) * (↑$nd : ENNReal)) => return true

  -- Nested patterns
  | ~q(($a * $b : ENNReal) / $c = $d) => return true
  | ~q(($a : ENNReal) / ($b * $c) = $d) => return true
  | ~q(($a : ENNReal) = ($b * $c) / $d) => return true
  | ~q(($a : ENNReal) = $b / ($c * $d)) => return true

  | _ => return false

syntax "ennreal_mul_div_assoc" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    let hasMultInDiv ← analyzeMultiplicationInDivision target
    let basicPattern? ← analyzeBasicArithmeticPattern target

    match basicPattern? with
    | some (hasAddition, hasMultiplication, hasDivision, hasInverse) =>
      let hasSimpleArith := (hasAddition || hasMultiplication) && !hasDivision && !hasInverse

      if hasMultInDiv then
        if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return
      else if hasSimpleArith then
        if ← tryTactic (← `(tactic| norm_num)) then return
        if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, Nat.cast_mul])) then return

      if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return

      if ← tryTacticSequence [
        ← `(tactic| apply ENNReal.div_self),
        ← `(tactic| apply Nat.cast_ne_zero.mpr),
        ← `(tactic| assumption),
        ← `(tactic| exact ENNReal.coe_ne_top)
      ] then return

    | none =>
      throwError "ennreal_mul_div_assoc expects an equality goal"

    throwError "ennreal_mul_div_assoc could not solve the goal"

syntax "ennreal_inv_transform" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryTactic (← `(tactic| rfl)) then return

    let invPattern? ← analyzeInversePattern target
    let hasMultInDiv ← analyzeMultiplicationInDivision target

    match invPattern? with
    | some (hasInverse, hasDoubleInverse, hasInverseWithDivision, _) =>
      if hasDoubleInverse then
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, one_div])) then return

      if hasInverseWithDivision then
        if ← tryTactic (← `(tactic| simp only [div_eq_mul_inv, mul_comm, inv_eq_one_div])) then return

      if hasInverse && !hasInverseWithDivision then
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul, mul_comm])) then return
        if ← tryTactic (← `(tactic| rw [← div_eq_mul_inv])) then return

      if hasMultInDiv then
        if ← tryTacticSequence [
          ← `(tactic| simp only [one_div, inv_inv]),
          ← `(tactic| ennreal_mul_div_assoc)
        ] then return

      if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                             div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul, one_div])) then return

    | none =>
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div])) then return

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

syntax "ennreal_fraction_add" : tactic

elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryTactic (← `(tactic| norm_num)) then return

    if ← isConcreteDivisionGoal target then
      if ← tryTactic (← `(tactic| ennreal_div_self)) then return

    -- Use QQ pattern matching for specific common patterns first
    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q(($a : ENNReal) / $den + ($b : ENNReal) / $den2 = ($c : ENNReal) / $den3) =>
      if (← isDefEq den den2) && (← isDefEq den den3) then
      if ← tryTactic (← `(tactic| rw [← ENNReal.add_div])) then return
      if ← tryTactic (← `(tactic| norm_num)) then return

    | ~q(($a : ENNReal) + $b = $c) =>
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

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by ennreal_fraction_add

end ENNRealArith
