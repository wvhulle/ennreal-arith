import ENNRealArith.Common
import Qq

open Lean Meta Elab Tactic ENNReal Qq

namespace ENNRealArith

/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`,
as well as concrete cases like `18 / 18 = 1`.
-/

elab "ennreal_div_self" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    unless target.isAppOfArity ``Eq 3 do
      throwError "ennreal_div_self expects an equality goal"

    let applyDivSelf : TacticM Unit := do
      evalTactic (← `(tactic| apply ENNReal.div_self))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      tryNonzeroProof
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))

    try
      applyDivSelf
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    have targetQ : Q(ENNReal) := target
    match targetQ with
    | ~q(($a : ENNReal) / $b) =>
      if ← isDefEq a b then
        try applyDivSelf catch _ => pure ()
    | _ => pure ()


/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/


elab "ennreal_mul_cancel" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero,
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q((↑($a * $c) : ENNReal) / (↑($b * $c2) : ENNReal) = (↑$a2 : ENNReal) / (↑$b2 : ENNReal)) =>
      if (← isDefEq c c2) && (← isDefEq a a2) && (← isDefEq b b2) then

        let cancelTactics := [
          (← `(tactic| apply ENNReal.mul_div_mul_right)),
          (← `(tactic| apply ENNReal.mul_div_mul_left))
        ]

        for cancelTactic in cancelTactics do
          try
            evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
            evalTactic cancelTactic
            evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
            evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
            tryNonzeroProof
            evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
            if (← getUnsolvedGoals).isEmpty then return
          catch _ => pure ()

    | _ => pure ()

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

    throwError "ennreal_mul_cancel could not solve the goal"

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel

end ENNRealArith
