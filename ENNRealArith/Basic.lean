import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Expr
import Lean.PrettyPrinter
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Lean
import Lean.Util.Trace

open Lean Meta Elab Tactic ENNReal Qq

initialize
  registerTraceClass `ENNRealArith
  registerTraceClass `ENNRealArith.conversion
  registerTraceClass `ENNRealArith.lifting
  registerTraceClass `ENNRealArith.debug
  registerTraceClass `ENNRealArith.final


namespace ENNRealArith

/-!
Count occurrences of ENNReal.ofReal in an expression
-/
partial def countOfRealOccurrences (e : Expr) : Nat := Id.run do
  let mut count := 0
  if e.isAppOf ``ENNReal.ofReal then
    count := count + 1
  for arg in e.getAppArgs do
    count := count + countOfRealOccurrences arg
  return count

/-!
Check if an expression is a literal or simple ENNReal.ofReal application
-/
def isLiteralOrSimpleOfReal (e : Expr) : Bool := Id.run do
  if e.isAppOf ``ENNReal.ofReal then
    return true

  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args.size >= 3 then
      let typeArg := args[0]!
      let numArg := args[1]!
      return typeArg.isAppOf ``ENNReal && numArg.isLit

  if e.isAppOf ``Nat.cast then
    let args := e.getAppArgs
    if args.size >= 3 then
      let typeArg := args[1]!
      let numArg := args[2]!
      return typeArg.isAppOf ``ENNReal && numArg.isLit

  return false

/-!
Check if the goal is ready for final computation:
- Must be an equality
- Both sides must be literals or simple ENNReal.ofReal applications
-/
def isReadyForFinalComputation (goalType : Expr) : TacticM Bool := do
  -- Check if it's an equality (Eq)
  if !goalType.isAppOf ``Eq then return false

  let args := goalType.getAppArgs
  if args.size < 3 then return false

  let lhs := args[1]!  -- Left-hand side
  let rhs := args[2]!  -- Right-hand side

  let lhsReady := isLiteralOrSimpleOfReal lhs
  let rhsReady := isLiteralOrSimpleOfReal rhs

  trace[ENNRealArith.debug] "LHS ready: {lhsReady}, RHS ready: {rhsReady} | LHS: {lhs}, RHS: {rhs}"

  return lhsReady && rhsReady

/-!
Recursively find all ENNReal expressions in a term that look like finite literals.
Specifically looks for patterns like: @OfNat.ofNat ℝ≥0∞ 5000 instOfNatAtLeastTwo : ℝ≥0∞
-/
partial def findENNRealLiterals (e : Expr) : Array Expr := Id.run do
  let mut literals := #[]

  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args.size >= 3 then
      let typeArg := args[0]!
      let numArg := args[1]!
      if typeArg.isAppOf ``ENNReal && numArg.isLit then
        literals := literals.push e

  if e.isAppOfArity ``Coe.coe 3 then
    let args := e.getAppArgs
    if args.size >= 3 then
      let target := args[1]!
      if target.isAppOf ``ENNReal then
        let source := args[2]!
        if source.isLit then
          literals := literals.push e

  for arg in e.getAppArgs do
    literals := literals ++ findENNRealLiterals arg

  return literals


elab "eq_as_reals" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let literals := findENNRealLiterals goalType
  if literals.isEmpty then
    trace[ENNRealArith.info] "No ENNReal literals found in the goal."
    return ()


  for lit in literals do
    try
      let litSyntax ←  lit.toSyntax
      evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $litSyntax ≠ ⊤)]))
      evalTactic (← `(tactic| simp only [ENNReal.toReal_ofNat]))
      trace[ENNRealArith.conversion] m!"Converted {lit} to Real: {← getMainGoal}"
    catch _ =>
      trace[ENNRealArith.conversion] m!"Failed to convert literal {lit}, skipping"
      continue

  trace[conversion] m!"Starting lifting phases: {← getMainGoal}"
  let maxIterations := 10
  for _ in List.range maxIterations do


    let liftingPhases := [
      ← `(tactic| (rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)])),
      ← `(tactic| (rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)])),
      ← `(tactic| (rw [← ENNReal.ofReal_mul])),
      ← `(tactic| (rw [← ENNReal.ofReal_add])),
      ← `(tactic| (rw [← ENNReal.ofReal_one])),
      ← `(tactic| (rw [← ENNReal.ofReal_zero])),
    ]

    for phase in liftingPhases do
      let goal ← getMainGoal
      let goalTypeBefore ← goal.getType
      let ofRealCountBefore := countOfRealOccurrences goalTypeBefore
      try
        evalTactic phase
        let goalAfter ← getMainGoal
        let goalTypeAfter ← goalAfter.getType
        let ofRealCountAfter := countOfRealOccurrences goalTypeAfter
        trace[ENNRealArith.lifting] "Applied phase ({ofRealCountBefore}→{ofRealCountAfter}): {goalAfter}"

        if ← isReadyForFinalComputation goalTypeAfter then
          trace[ENNRealArith.lifting] "Ready for final computation"
          break
      catch _ =>
        trace[ENNRealArith.lifting] "Phase failed, continuing"
        continue
    let goalAfter ← getMainGoal
    let goalTypeAfter ← goalAfter.getType
    if ← isReadyForFinalComputation goalTypeAfter then
          trace[ENNRealArith.lifting] "Ready for final computation after iteration"
          break

  trace[ENNRealArith.final] "Starting final computation phase"

  try
    evalTactic (← `(tactic| all_goals norm_num))
    let goals ← getUnsolvedGoals
    if goals.isEmpty then
      trace[ENNRealArith.final] "Successfully solved with norm_num"
      return
  catch _ =>
    trace[ENNRealArith.final] "Final computation failed"
    pure ()



lemma inv_div_eq_div {a b : ℕ} : (↑a : ENNReal)⁻¹ / (↑b : ENNReal)⁻¹ = ↑b / ↑a := by
   calc
      (↑a : ENNReal)⁻¹ / (↑b : ENNReal)⁻¹
      _ = (↑a : ENNReal)⁻¹ * ((↑b : ENNReal)⁻¹)⁻¹ := by
        rw [div_eq_mul_inv]
      _ = (↑b : ENNReal) * (↑a)⁻¹ := by
        rw [inv_inv]
        rw [mul_comm]
      _ = ↑b / ↑a := by
        rw [<- div_eq_mul_inv]


lemma add_mixed_denom {a b c d : ENNReal} {hc : c ≠ 0} {hd : d ≠ 0} {hct: c ≠ ⊤} {hdt: d ≠ ⊤} :
  a / c + b / d = (a * d + b * c) / (c * d)  := by
    have h1 : a / c = (a * d) / (c * d) := by
      rw [<- ENNReal.mul_div_mul_right] <;> norm_num
      · assumption
      · assumption
    have h2 : b / d = (b * c) / (c * d) := by
      rw [mul_comm c d]
      rw [<- ENNReal.mul_div_mul_right] <;> norm_num
      · assumption
      · assumption
    rw [h1, h2]
    rw [← ENNReal.div_add_div_same]


lemma div_div_cast {a b c : ℕ}:
  ((↑a : ENNReal) / ↑b) / ↑c = ↑a / (↑b * ↑c) := by
  calc ((↑a : ENNReal) / ↑b) / ↑c
    _ = (↑a : ENNReal) / ↑b * (↑c)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (↑a : ENNReal) * (↑b)⁻¹ * (↑c)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (↑a : ENNReal) * ((↑b)⁻¹ * (↑c)⁻¹) := by
      rw [mul_assoc]
    _ = (↑a : ENNReal) * ((↑b * ↑c)⁻¹) := by
      congr 1
      rw [ENNReal.mul_inv]
      all_goals norm_num
    _ = (↑a : ENNReal) / (↑b * ↑c) := by
      rw [← div_eq_mul_inv]


lemma div_div {a b c : ENNReal} {h: b ≠ 0} {g: c ≠ 0}:
  (a / b) / c = a / (b * c) := by
  calc (a / b) / c
    _ = (a / b) * c⁻¹ := by
      rw [div_eq_mul_inv]
    _ = a * b⁻¹ * c⁻¹ := by
      rw [div_eq_mul_inv]
    _ = a  * ((b)⁻¹ * (c)⁻¹) := by
      rw [mul_assoc]
    _ = a * ((b * c)⁻¹) := by
      congr 1
      rw [ENNReal.mul_inv]
      . exact Or.inl h
      . exact Or.inr g
    _ = a   / (b * c) := by
      rw [← div_eq_mul_inv]


lemma add_div_eq_div {a b c  : ENNReal} {hc : c ≠ 0}  {hct: c ≠ ⊤}  :
  a + b / c = (a * c + b ) / c  := by
    have h1 : a = (a * c) / c := by
      exact Eq.symm (ENNReal.mul_div_cancel_right hc hct)
    rw [h1]

    rw [ENNReal.div_add_div_same]
    rw [ENNReal.div_eq_div_iff]
    rw [mul_div_assoc]
    rw [ENNReal.div_self]
    ring
    all_goals assumption


lemma div_eq_iff {a b c : ENNReal} {hc : c ≠ 0} {hct: c ≠ ⊤} :
  a / c = b ↔ a = b * c := by
    constructor
    · intro h
      rw [<- ENNReal.mul_right_inj hc] at h
      have: c * ( a / c ) = c * a / c := by
        exact Eq.symm (mul_div_assoc c a c)
      rw [this] at h
      rw [mul_comm] at h
      rw [ENNReal.mul_div_cancel_right hc hct] at h
      rw [mul_comm] at h
      exact h
      assumption
    · intro h
      rw [h]
      rw [ENNReal.mul_div_cancel_right hc hct]


lemma eq_as_real {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]
