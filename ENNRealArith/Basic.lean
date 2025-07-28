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
  registerTraceClass `ENNRealArith.search
  registerTraceClass `ENNRealArith.conversion
  registerTraceClass `ENNRealArith.lifting
  registerTraceClass `ENNRealArith.debug
  registerTraceClass `ENNRealArith.final


namespace ENNRealArith

/-!
Count occurrences of ENNReal.ofReal in an expression
-/
partial def countOfRealOccurrences (e : Expr) : Nat :=
  let count := if e.isAppOf ``ENNReal.ofReal then 1 else 0
  count + e.getAppArgs.foldl (fun acc arg => acc + countOfRealOccurrences arg) 0

/-!
Check if an expression is a literal or simple ENNReal.ofReal application
-/
def fullyLifted (e : Expr) : Bool := Id.run do
  -- Check for ENNReal.ofReal pattern
  if e.isAppOf ``ENNReal.ofReal then
    return true

  -- Check for OfNat.ofNat pattern with literal
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args.size >= 3 then
      return args[0]!.isAppOf ``ENNReal && args[1]!.isLit

  -- Check for Nat.cast pattern with literal
  if e.isAppOfArity ``Nat.cast 2 then
    let args := e.getAppArgs
    if args.size >= 2 then
      return args[0]!.isAppOf ``ENNReal && args[1]!.isLit

  return false

/-!
Check if the goal is ready for final computation:
- Must be an equality or inequality
- Both sides must be literals or simple ENNReal.ofReal applications
-/
def isReadyForFinalComputation (goalType : Expr) : Bool :=
  let isEq := goalType.isAppOfArity ``Eq 3
  let isLt := goalType.isAppOfArity ``LT.lt 3
  let isLe := goalType.isAppOfArity ``LE.le 3
  let isGt := goalType.isAppOfArity ``GT.gt 3
  let isGe := goalType.isAppOfArity ``GE.ge 3
  (isEq || isLt || isLe || isGt || isGe) &&
    let args := goalType.getAppArgs
    args.size >= 3 && fullyLifted args[1]! && fullyLifted args[2]!


structure FiniteVar where
  expr : Expr
  proof : Expr



def maybeFiniteFVar (e: Expr) : MetaM (Option FiniteVar) := do
  if !e.isFVar then return none
  let ctx ← getLCtx
  ctx.findDeclM? fun decl => do
    if decl.isImplementationDetail then return none
    let declType := decl.type

    -- Pattern matching for finiteness proofs
    match isFinitePattern e declType with
    | true => return some (FiniteVar.mk e decl.toExpr)
    | false => return none
where
  isFinitePattern (e : Expr) (declType : Expr) : Bool :=
    -- Check for e ≠ ⊤ pattern
    (declType.isAppOfArity ``Ne 3 &&
      let args := declType.getAppArgs
      args.size >= 3 && args[1]! == e && args[2]!.isAppOfArity ``Top.top 2) ||
    -- Check for ¬(e = ⊤) pattern
    (declType.isAppOfArity ``Not 1 &&
      let eqExpr := declType.getAppArgs[0]!
      eqExpr.isAppOfArity ``Eq 3 &&
      let args := eqExpr.getAppArgs
      args.size >= 3 && args[1]! == e && args[2]!.isAppOfArity ``Top.top 2)




inductive ENNRealExpr
| finite_var: FiniteVar → ENNRealExpr
| other: Expr → ENNRealExpr

/-!
Recursively find all ENNReal expressions in a term that look like finite literals.
Specifically looks for patterns like: @OfNat.ofNat ℝ≥0∞ 5000 instOfNatAtLeastTwo : ℝ≥0∞
-/
partial def findENNVarExpr (e : Expr) : MetaM (Array ENNRealExpr) := do
  let mut literals := #[]

  -- Debug: trace the structure of expressions we're examining
  try
    let exprType ← inferType e
    if exprType.isAppOf ``ENNReal then
      trace[ENNRealArith.search] m!"Examining ENNReal expression: {e}"
      trace[ENNRealArith.search] m!"Expression structure: {e.ctorName}"
      if e.isApp then
        trace[ENNRealArith.search] m!"App function: {e.getAppFn}, args: {e.getAppArgs}"
  catch _ =>
    -- If we can't infer the type, skip this expression
    pure ()

  if e.isFVar then
    try
      if let some finite_var <- maybeFiniteFVar e then
        literals := literals.push (ENNRealExpr.finite_var finite_var)
    catch _ =>
      pure ()

  -- Check for OfNat.ofNat pattern
  try
    if e.isAppOfArity ``OfNat.ofNat 3 then
      let args := e.getAppArgs
      if args.size >= 3 then
        let typeArg := args[0]!
        let numArg := args[1]!
        if typeArg.isAppOf ``ENNReal && numArg.isLit then
          literals := literals.push (ENNRealExpr.other e)
  catch _ =>
    pure ()

  -- Handle ENNReal.ofNNReal pattern for decimal/NNReal cases
  try
    if e.isApp && e.getAppFn.constName? == some ``ofNNReal then
      let args := e.getAppArgs
      if args.size >= 1 then
        let nnrealArg := args[0]!
        trace[ENNRealArith.search] m!"Found ofNNReal pattern, nnrealArg: {nnrealArg}"
        literals := literals.push (ENNRealExpr.other e)
  catch _ =>
    pure ()

  -- Recursively check subexpressions
  try
    match e with
    | .app f a =>
      literals := literals ++ (← findENNVarExpr f)
      literals := literals ++ (← findENNVarExpr a)
    | .lam _ _ b _ => literals := literals ++ (← findENNVarExpr b)
    | .forallE _ _ b _ => literals := literals ++ (← findENNVarExpr b)
    | .letE _ _ _ _ _ =>
      -- Handle let expressions properly by reducing them first
      let reducedExpr ← whnf e
      literals := literals ++ (← findENNVarExpr reducedExpr)
    | .mdata _ b => literals := literals ++ (← findENNVarExpr b)
    | .proj _ _ b => literals := literals ++ (← findENNVarExpr b)
    | _ => pure ()
  catch _ =>
    pure ()

  if ! literals.isEmpty then
    trace[ENNRealArith.search] m!"Found literals: {literals.map (fun l => match l with
      | ENNRealExpr.finite_var fv => fv.expr
      | ENNRealExpr.other e => e)}"

  return literals


def tryReflexiveGoal (goalType : Expr) : TacticM Bool := do
  if goalType.getAppArgs.size < 3 then return false

  let lhs := goalType.getAppArgs[1]!
  let rhs := goalType.getAppArgs[2]!

  if lhs != rhs then return false

  let reflexiveRelations := [``Eq, ``LE.le, ``GE.ge]
  let isReflexiveRelation := reflexiveRelations.any (goalType.isAppOf ·)

  if isReflexiveRelation then
    evalTactic (← `(tactic| rfl))
    return true
  else
    return false

def processENNExpressions (goalType : Expr) : TacticM Unit := do
  let enn_expressions <- findENNVarExpr goalType
  for enn_expr in enn_expressions do
    try
      match enn_expr with
      | ENNRealExpr.finite_var finite_var =>
        let enn_expr := finite_var.expr
        let proof := finite_var.proof
        trace[ENNRealArith.conversion] m!"Found finiteness proof for {enn_expr}: {proof}"
        let proofSyntax ← proof.toSyntax
        evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal $proofSyntax]))
      | ENNRealExpr.other enn_expr =>
        trace[ENNRealArith.conversion] m!"No finiteness proof found for {enn_expr}, trying norm_num"
        let enn_syntax ← enn_expr.toSyntax
        evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $enn_syntax ≠ ⊤)]))
    catch _ =>
      continue

def runLiftingPhases : TacticM Unit := do
  trace[ENNRealArith.lifting] m!"Starting lifting phases: {← getMainGoal}"
  let maxIterations := 10
  let mut previousGoalType : Option Expr := none
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

        try
          evalTactic (← `(tactic| simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))
        catch _ =>
          pure ()

        let goalAfter ← getMainGoal
        let goalTypeAfter ← goalAfter.getType
        let ofRealCountAfter := countOfRealOccurrences goalTypeAfter
        trace[ENNRealArith.lifting] m!"Applied phase {phase}, converted {goalTypeBefore} to {goalTypeAfter}, reduced {ofRealCountBefore} to {ofRealCountAfter} occurrences of ENNReal.ofReal"

        if isReadyForFinalComputation goalTypeAfter then
          trace[ENNRealArith.lifting] "Ready for final computation"
          break
      catch _ =>
        trace[ENNRealArith.lifting] m!"Phase {phase} failed, continuing"
        continue
    let goalAfter ← getMainGoal
    let goalTypeAfter ← goalAfter.getType

    match previousGoalType with
    | some prevType =>
      if prevType == goalTypeAfter then
        trace[ENNRealArith.lifting] "No progress made in this iteration, stopping"
        break
    | none => pure ()

    previousGoalType := some goalTypeAfter

    if isReadyForFinalComputation goalTypeAfter then
      trace[ENNRealArith.lifting] m!"Ready for final computation after iteration with goal {goalAfter}"
      break

def runFinalComputation (initialGoalState : Tactic.SavedState) : TacticM Unit := do
  trace[ENNRealArith.final] "Starting final computation phase"

  try
    evalTactic (← `(tactic|
      (first | congr 1 | rw [← ENNReal.toReal_lt_toReal_iff] | rw [← ENNReal.toReal_le_toReal_iff] | skip) <;>
      all_goals (first | apply ENNReal.toReal_nonneg | skip) <;>
      simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))
    let goal ← getMainGoal

    trace[ENNRealArith.final] m!"Applied Real conversion tactics, now solving for {goal}"

  catch e =>
    trace[ENNRealArith.final] m!"Could not handle ofReal conversion: {e.toMessageData}"

  try
    let goal ← getMainGoal
    trace[ENNRealArith.final] m!"Final computation on goal with norm_num: {goal}"

    -- First try congr to see what we get
    evalTactic (← `(tactic| all_goals (congr 1)))


    evalTactic (← `(tactic| all_goals norm_num))

    let remainingGoals ← getUnsolvedGoals
    if !remainingGoals.isEmpty then
      let goal ← getMainGoal
      let goalType ← goal.getType
      trace[ENNRealArith.final] m!"norm_num left unsolved goal: {goalType}"
      evalTactic (← `(tactic| all_goals ring_nf))
    let finalGoals ← getUnsolvedGoals
    if finalGoals.isEmpty then
      trace[ENNRealArith.final] "Successfully solved with norm_num/ring"
      return
    else
      restoreState initialGoalState
      throwError "eq_as_reals failed: Could not prove the goal using real arithmetic."
  catch e =>
    trace[ENNRealArith.final] m!"Final computation failed with error: {e.toMessageData}"
    try
      restoreState initialGoalState
      trace[ENNRealArith.final] "Trying ENNReal algebraic fallback tactics"
      evalTactic (← `(tactic| first | ac_rfl | ring_nf | skip))
      let goals ← getUnsolvedGoals
      if goals.isEmpty then
        trace[ENNRealArith.final] "Successfully solved with ENNReal algebraic fallback"
        return
    catch _ =>
      pure ()
    restoreState initialGoalState
    throwError "eq_as_reals failed: Could not prove the goal."

elab "eq_as_reals" : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let initialGoalState ← saveState

    let goalType ← whnf goalType

    if ← tryReflexiveGoal goalType then
      return

    processENNExpressions goalType

    runLiftingPhases

    runFinalComputation initialGoalState



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
