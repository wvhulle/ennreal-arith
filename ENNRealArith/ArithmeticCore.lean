import ENNRealArith.Common
import Qq

open Lean Meta Elab Tactic
open ENNReal Qq

namespace ENNRealArith


/--
Analyzes patterns for basic arithmetic operations using QQ pattern matching.
Returns booleans for: hasAddition, hasMultiplication, hasDivision, hasInverse
-/
def analyzeBasicArithmeticPattern (target : Expr) : MetaM (Option (Bool × Bool × Bool × Bool)) := do
  -- Check that we have a Prop goal
  let targetType ← inferType target
  unless ← isDefEq targetType q(Prop) do
    return none

  -- Use QQ pattern matching on the target
  have targetQ : Q(Prop) := target
  match targetQ with

  -- Addition patterns
  | ~q(($a : ENNReal) + $b = $c) => return some (true, false, false, false)
  | ~q(($a : ENNReal) = $b + $c) => return some (true, false, false, false)
  | ~q((↑$na : ENNReal) + (↑$nb : ENNReal) = $c) => return some (true, false, false, false)
  | ~q(($a : ENNReal) = (↑$nb : ENNReal) + (↑$nc : ENNReal)) => return some (true, false, false, false)

  -- Multiplication patterns
  | ~q(($a : ENNReal) * $b = $c) => return some (false, true, false, false)
  | ~q(($a : ENNReal) = $b * $c) => return some (false, true, false, false)
  | ~q((↑$na : ENNReal) * (↑$nb : ENNReal) = $c) => return some (false, true, false, false)
  | ~q(($a : ENNReal) = (↑$nb : ENNReal) * (↑$nc : ENNReal)) => return some (false, true, false, false)

  -- Division patterns
  | ~q(($a : ENNReal) / $b = $c) => return some (false, false, true, false)
  | ~q(($a : ENNReal) = $b / $c) => return some (false, false, true, false)
  | ~q((↑$na : ENNReal) / (↑$nb : ENNReal) = $c) => return some (false, false, true, false)
  | ~q(($a : ENNReal) = (↑$nb : ENNReal) / (↑$nc : ENNReal)) => return some (false, false, true, false)

  -- Inverse patterns
  | ~q((($a : ENNReal)⁻¹) = $b) => return some (false, false, false, true)
  | ~q(($a : ENNReal) = (($b)⁻¹)) => return some (false, false, false, true)

  -- Combined patterns - addition with multiplication
  | ~q(($a : ENNReal) + $b * $c = $d) => return some (true, true, false, false)
  | ~q(($a : ENNReal) * $b + $c = $d) => return some (true, true, false, false)
  | ~q(($a : ENNReal) = $b + $c * $d) => return some (true, true, false, false)
  | ~q(($a : ENNReal) = $b * $c + $d) => return some (true, true, false, false)

  -- Combined patterns - addition with division
  | ~q(($a : ENNReal) + $b / $c = $d) => return some (true, false, true, false)
  | ~q(($a : ENNReal) / $b + $c = $d) => return some (true, false, true, false)
  | ~q(($a : ENNReal) = $b + $c / $d) => return some (true, false, true, false)
  | ~q(($a : ENNReal) = $b / $c + $d) => return some (true, false, true, false)

  -- Combined patterns - multiplication with division
  | ~q(($a : ENNReal) * $b / $c = $d) => return some (false, true, true, false)
  | ~q(($a : ENNReal) / $b * $c = $d) => return some (false, true, true, false)
  | ~q(($a : ENNReal) = $b * $c / $d) => return some (false, true, true, false)
  | ~q(($a : ENNReal) = $b / $c * $d) => return some (false, true, true, false)

  -- Combined patterns - addition with inverse
  | ~q(($a : ENNReal) + (($b)⁻¹) = $c) => return some (true, false, false, true)
  | ~q((($a : ENNReal)⁻¹) + $b = $c) => return some (true, false, false, true)
  | ~q(($a : ENNReal) = $b + (($c)⁻¹)) => return some (true, false, false, true)
  | ~q(($a : ENNReal) = (($b)⁻¹) + $c) => return some (true, false, false, true)

  -- Combined patterns - multiplication with inverse
  | ~q(($a : ENNReal) * (($b)⁻¹) = $c) => return some (false, true, false, true)
  | ~q((($a : ENNReal)⁻¹) * $b = $c) => return some (false, true, false, true)
  | ~q(($a : ENNReal) = $b * (($c)⁻¹)) => return some (false, true, false, true)
  | ~q(($a : ENNReal) = (($b)⁻¹) * $c) => return some (false, true, false, true)

  -- Combined patterns - division with inverse
  | ~q(($a : ENNReal) / (($b)⁻¹) = $c) => return some (false, false, true, true)
  | ~q((($a : ENNReal)⁻¹) / $b = $c) => return some (false, false, true, true)
  | ~q(($a : ENNReal) = $b / (($c)⁻¹)) => return some (false, false, true, true)
  | ~q(($a : ENNReal) = (($b)⁻¹) / $c) => return some (false, false, true, true)

  -- Complex combined patterns
  | ~q(($a : ENNReal) + $b * $c / $d = $e) => return some (true, true, true, false)
  | ~q(($a : ENNReal) * $b + $c / $d = $e) => return some (true, true, true, false)
  | ~q(($a : ENNReal) / $b + $c * $d = $e) => return some (true, true, true, false)
  | ~q(($a : ENNReal) = $b + $c * $d / $e) => return some (true, true, true, false)
  | ~q(($a : ENNReal) = $b * $c + $d / $e) => return some (true, true, true, false)
  | ~q(($a : ENNReal) = $b / $c + $d * $e) => return some (true, true, true, false)

  -- Simple equality (no arithmetic operations)
  | ~q(($a : ENNReal) = $b) => return some (false, false, false, false)
  | ~q((↑$na : ENNReal) = (↑$nb : ENNReal)) => return some (false, false, false, false)

  | _ => return none

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

    let patterns? ← analyzeBasicArithmeticPattern target
    match patterns? with
    | some (hasAddition, hasMultiplication, hasDivision, hasInverse) =>
      let simpleArith := (hasAddition || hasMultiplication) && !hasDivision && !hasInverse

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


    try
      evalTactic (← `(tactic| apply ENNReal.div_self))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      tryNonzeroProof
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    have targetQ : Q(ENNReal) := target

    match targetQ with
      | ~q(($a : ENNReal) / $b) =>
        if ← isDefEq a b then
          try
            evalTactic (← `(tactic| apply ENNReal.div_self))
            evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
            evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
            tryNonzeroProof
            evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
          catch _ => pure ()


/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/
syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero,
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    -- Use QQ pattern matching for the entire target
    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q((↑$lhsNumNat : ENNReal) / (↑$lhsDenNat : ENNReal) = (↑$rhsNumNat : ENNReal) / (↑$rhsDenNat : ENNReal)) =>

          match lhsNumNat, lhsDenNat with
          | ~q($a * $c), ~q($b * $c2) =>
            if (← isDefEq c c2) && (← isDefEq a rhsNumNat) && (← isDefEq b rhsDenNat) then


              -- Second try: Apply cancellation rules
              try
                evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
                evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
                evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
                evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
                tryNonzeroProof
                evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
                if (← getUnsolvedGoals).isEmpty then return
              catch _ => pure ()

              -- Third try: Left cancellation
              try
                evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
                evalTactic (← `(tactic| apply ENNReal.mul_div_mul_left))
                evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
                evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
                tryNonzeroProof
                evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
                if (← getUnsolvedGoals).isEmpty then return
              catch _ => pure ()
          | _ => pure () -- No cancellation pattern detected
    | _ => pure () -- Not a cancellation goal
    -- Fallback: Try generic cancellation approaches regardless of pattern detection
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

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel

end ENNRealArith
