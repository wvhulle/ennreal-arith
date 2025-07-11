import ENNRealArith.Common
import Qq

open Lean Meta Elab Tactic ENNReal Qq

namespace ENNRealArith

/-- Convert an ENNReal equation to a Real equation when both sides are not infinity -/
lemma ennreal_eq_via_toReal {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]

/-- Helper to prove that a casted natural number is non-zero in ENNReal -/
def proveENNRealCoeNonzero : TacticM Unit := do
  evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
  evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
  tryNonzeroProof



/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`,
as well as concrete cases like `18 / 18 = 1`.
-/
elab "ennreal_div_self" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q(($a : ENNReal) / $a = 1) =>
      -- Direct self-division pattern
      evalTactic (← `(tactic| apply ENNReal.div_self))
      proveENNRealCoeNonzero
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      return
    | ~q(($a : ENNReal) / $b = 1) =>
      if ← isDefEq a b then
        evalTactic (← `(tactic| apply ENNReal.div_self))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return
    | _ => pure ()



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

    evalTactic (← `(tactic| first | apply ENNReal.div_self | apply Nat.cast_ne_zero.mpr | assumption | exact ENNReal.coe_ne_top))


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




end ENNRealArith
