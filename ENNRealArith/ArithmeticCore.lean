import ENNRealArith.Common

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for basic ENNReal simplifications using norm_num, norm_cast, and simp.
Tries various combinations of these tactics to solve simple arithmetic goals.
-/
syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if ← tryBasicComputation then return
    let patterns? ← analyzeEqualityGoal target

    match patterns? with
    | some (lhs, rhs) =>
      let simpleArith := lhs.isSimpleArithmetic && rhs.isSimpleArithmetic
      let hasDivision := lhs.hasDivision || rhs.hasDivision
      let hasInverse := lhs.hasInverse || rhs.hasInverse

      if simpleArith then
        if ← tryTactic (← `(tactic| norm_num)) then return
        if ← tryTactic (← `(tactic| simp only [add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul])) then return
        if ← tryTacticSequence [← `(tactic| norm_cast), ← `(tactic| norm_num)] then return
      else if hasDivision then
        if ← tryTactic (← `(tactic| simp only [ENNReal.zero_div, div_one])) then return
        if ← tryTacticSequence [← `(tactic| rw [ENNReal.div_eq_div_iff]), ← `(tactic| all_goals norm_num)] then return
      else if hasInverse then
        if ← tryTactic (← `(tactic| simp only [inv_eq_one_div, inv_inv])) then return

      if ← tryTactic (← `(tactic| simp [ENNReal.add_eq_top, ENNReal.mul_eq_top])) then return
    | none =>
      if ← tryTactic (← `(tactic| simp)) then return

    let tacticSequences := [
      [← `(tactic| norm_cast), ← `(tactic| norm_num)],
      [← `(tactic| simp only [add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul])],
      [← `(tactic| simp only [add_zero, zero_add, mul_zero, zero_mul]), ← `(tactic| norm_num)],
      [← `(tactic| norm_num)]
    ]

    for sequence in tacticSequences do
      if ← tryTacticSequence sequence then return

    throwError "ennreal_basic_simp could not solve the goal"

/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`,
as well as concrete cases like `18 / 18 = 1`.
-/
syntax "ennreal_div_self" : tactic

elab_rules : tactic | `(tactic| ennreal_div_self) =>  do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    if !target.isAppOfArity ``Eq 3 then
      throwError "ennreal_div_self expects an equality goal"

    let lhs := target.getArg! 1
    let _rhs := target.getArg! 2

    try
      evalTactic (← `(tactic| apply ENNReal.div_self))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      tryNonzeroProof
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    if lhs.isAppOfArity ``HDiv.hDiv 6 then
      let num := lhs.getArg! 4
      let den := lhs.getArg! 5

      if num == den then
        try
          evalTactic (← `(tactic| apply ENNReal.div_self))
          evalTactic (← `(tactic| norm_num))
          evalTactic (← `(tactic| norm_num))
          if (← getUnsolvedGoals).isEmpty then return
        catch _ => pure ()

    throwError "ennreal_div_self could not solve the goal"

/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/
syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
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

      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => pure ()

      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_left))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    if ← attemptCancellation then return

    throwError "ennreal_mul_cancel could not solve the goal"

end ENNRealArith
