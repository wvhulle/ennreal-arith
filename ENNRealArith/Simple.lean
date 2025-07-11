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



elab "ennreal_mul_div_assoc": tactic => do
  evalTactic (← `(tactic| first
    | (simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul]; done)
    | (norm_num; done)
    | (simp only [mul_one, one_mul, Nat.cast_mul]; done)
    | (apply ENNReal.div_self; apply Nat.cast_ne_zero.mpr; first | assumption | norm_num; exact ENNReal.coe_ne_top)))


elab "ennreal_inv_transform" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    try
      evalTactic (← `(tactic| rfl))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q((($a : ENNReal)⁻¹) * $b = $c) =>
      evalTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul, mul_comm]))
      try
        evalTactic (← `(tactic| rw [← div_eq_mul_inv]))
      catch _ => return
      return
    | _ => pure ()


    try
      evalTactic (← `(tactic| first
        | (rw [inv_inv]; done)
        | simp only [mul_div, Nat.cast_mul]
        ))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    evalTactic (← `(tactic| rw [ENNReal.div_eq_div_iff]; all_goals norm_num))

    evalTactic (← `(tactic| all_goals assumption))




end ENNRealArith
