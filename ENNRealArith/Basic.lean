import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Expr
import Lean.PrettyPrinter
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Lean
import Lean.Util.Trace
import ENNRealArith.Properties

open Lean Meta Elab Tactic ENNReal Qq

initialize
  registerTraceClass `ENNRealArith
  registerTraceClass `ENNRealArith.expr_search
  registerTraceClass `ENNRealArith.enn_conversion
  registerTraceClass `ENNRealArith.ofreal_lifting
  registerTraceClass `ENNRealArith.debug
  registerTraceClass `ENNRealArith.real_computation


namespace ENNRealArith

partial def countOfRealOccurrences (e : Expr) : Nat :=
  (if e.isAppOf ``ENNReal.ofReal then 1 else 0) +
  e.getAppArgs.foldl (· + countOfRealOccurrences ·) 0

def fullyLifted (e : Expr) : Bool :=
  match e with
  | .app (.const ``ENNReal.ofReal _) _ => true
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``ENNReal _)) (.lit _)) _ => true
  | .app (.app (.const ``Nat.cast _) (.const ``ENNReal _)) (.lit _) => true
  | .app (.const ``Top.top _) (.const ``ENNReal _) => true
  | _ => false

def isReadyForFinalComputation (goalType : Expr) : Bool :=
  let relations := [``Eq, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge]
  let args := goalType.getAppArgs
  relations.any (goalType.isAppOfArity · 3) &&
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
    if isFinitePattern e declType then
      return some (FiniteVar.mk e decl.toExpr)
    else
      return none
where
  isFinitePattern (e : Expr) (declType : Expr) : Bool :=
    match declType with
    | .app (.app (.app (.const ``Ne _) _) lhs) (.app (.const ``Top.top _) _) => lhs == e
    | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) _) lhs) (.app (.const ``Top.top _) _)) => lhs == e
    | _ => false




inductive ENNRealExpr
| finite_var: FiniteVar → ENNRealExpr
| other: Expr → ENNRealExpr

partial def findENNVarExpr (e : Expr) : MetaM (Array ENNRealExpr) := do
  let mut literals := #[]

  match e with
  | .fvar _ =>
    if let some finite_var ← maybeFiniteFVar e then
      literals := literals.push (ENNRealExpr.finite_var finite_var)
      trace[ENNRealArith.expr_search] m!"Found finite variable: {finite_var.expr}"
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``ENNReal _)) (.lit _)) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal literal: {e}"
  | .app (.const ``ofNNReal _) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ofNNReal expression: {e}"
  | .app (.app (.const ``Sup.sup _) _) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal supremum: {e}"
  | .app (.app (.const ``Inf.inf _) _) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal infimum: {e}"
  | .app (.app (.const ``HSub.hSub _) _) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal subtraction: {e}"
  | .app (.app (.const ``Sub.sub _) _) _ =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal subtraction: {e}"
  | .app (.const ``Top.top _) (.const ``ENNReal _) =>
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ENNReal infinity: {e}"
  | .app (.app (.const ``Coe.coe _) _) _ => 
    if e.getAppArgs.any (·.constName? == some ``ENNReal) then
      literals := literals.push (ENNRealExpr.other e)
      trace[ENNRealArith.expr_search] m!"Found ENNReal coercion: {e}"
  | _ => pure ()

  match e with
  | .app f a => literals := literals ++ (← findENNVarExpr f) ++ (← findENNVarExpr a)
  | .lam _ _ b _ | .forallE _ _ b _ | .mdata _ b | .proj _ _ b =>
    literals := literals ++ (← findENNVarExpr b)
  | .letE _ _ _ _ _ =>
    let reducedExpr ← whnf e
    literals := literals ++ (← findENNVarExpr reducedExpr)
  | _ => pure ()

  return literals


def tryReflexiveGoal (goalType : Expr) : TacticM Bool := do
  try
    let args := goalType.getAppArgs
    guard $ args.size >= 3
    guard $ args[1]! == args[2]!

    let reflexiveRelations := [``Eq, ``LE.le, ``GE.ge]
    guard $ reflexiveRelations.any (goalType.isAppOf ·)

    evalTactic (← `(tactic| rfl))
    return true
  catch _ =>
    return false

def processENNExpressions (goalType : Expr) : TacticM Unit := do
  let enn_expressions <- findENNVarExpr goalType
  trace[ENNRealArith.enn_conversion] m!"Found {enn_expressions.size} ENNReal expressions to convert"

  for enn_expr in enn_expressions do
    try
      match enn_expr with
      | ENNRealExpr.finite_var finite_var =>
        let enn_expr := finite_var.expr
        let proof := finite_var.proof
        trace[ENNRealArith.enn_conversion] m!"Converting finite var {enn_expr} with proof {proof}"
        let proofSyntax ← proof.toSyntax
        evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal $proofSyntax]))
      | ENNRealExpr.other enn_expr =>
        trace[ENNRealArith.enn_conversion] m!"Converting literal {enn_expr} with norm_num"
        let enn_syntax ← enn_expr.toSyntax
        evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $enn_syntax ≠ ⊤)]))
    catch _ =>
      continue

def runLiftingPhases : TacticM Unit := do
  trace[ENNRealArith.ofreal_lifting] m!"Starting ofReal lifting on: {← getMainGoal}"

  let liftingPhases := [
    ← `(tactic| rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_mul]),
    ← `(tactic| rw [← ENNReal.ofReal_add]),
    ← `(tactic| rw [← ENNReal.ofReal_one]),
    ← `(tactic| rw [← ENNReal.ofReal_zero])
  ]

  let mut previousGoalType : Option Expr := none
  for iteration in List.range 10 do
    trace[ENNRealArith.ofreal_lifting] m!"Lifting iteration {iteration + 1}"

    for phase in liftingPhases do
      try
        let goalBefore ← (← getMainGoal).getType
        let countBefore := countOfRealOccurrences goalBefore

        evalTactic phase
        try evalTactic (← `(tactic| simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))
        catch _ => pure ()

        let goalAfter ← (← getMainGoal).getType
        let countAfter := countOfRealOccurrences goalAfter

        if countAfter < countBefore then
          trace[ENNRealArith.ofreal_lifting] m!"Lifting progress: {countBefore} → {countAfter} ofReal occurrences"

        if isReadyForFinalComputation goalAfter then
          trace[ENNRealArith.ofreal_lifting] "Goal ready for final computation"
          break
      catch _ => continue

    let currentType ← (← getMainGoal).getType
    if some currentType == previousGoalType then
      trace[ENNRealArith.ofreal_lifting] "No progress made, stopping iterations"
      break
    previousGoalType := some currentType
    if isReadyForFinalComputation currentType then
      trace[ENNRealArith.ofreal_lifting] "Goal ready after iteration"
      break

def runFinalComputation (initialGoalState : Tactic.SavedState) : TacticM Unit := do
  trace[ENNRealArith.real_computation] "Converting ENNReal goal to Real arithmetic"

  let convertToReals := ← `(tactic|
    (first | congr 1 | rw [← ENNReal.toReal_lt_toReal_iff] | rw [← ENNReal.toReal_le_toReal_iff] | skip) <;>
    all_goals (first | apply ENNReal.toReal_nonneg | skip) <;>
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg])

  let solveWithArithmetic := ← `(tactic| all_goals (first | congr 1 ; norm_num | norm_num))
  let tryRingNormalization := ← `(tactic| all_goals ring_nf)
  let tryENNRealFallback := ← `(tactic| first | ac_rfl | ring_nf | skip)

  try
    evalTactic convertToReals
    trace[ENNRealArith.real_computation] m!"Real conversion successful: {← getMainGoal}"
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real conversion failed: {e.toMessageData}"

  try
    trace[ENNRealArith.real_computation] m!"Attempting norm_num on: {← getMainGoal}"
    evalTactic solveWithArithmetic

    let remainingGoals ← getUnsolvedGoals
    if !remainingGoals.isEmpty then
      trace[ENNRealArith.real_computation] m!"norm_num incomplete, trying ring_nf on: {← getMainGoal}"
      evalTactic tryRingNormalization

    if (← getUnsolvedGoals).isEmpty then
      trace[ENNRealArith.real_computation] "Successfully solved with real arithmetic"
      return

    restoreState initialGoalState
    throwError "eq_as_reals failed: Could not prove the goal using real arithmetic."
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real arithmetic failed: {e.toMessageData}"
    try
      restoreState initialGoalState
      trace[ENNRealArith.real_computation] "Trying ENNReal algebraic fallback"
      evalTactic tryENNRealFallback
      if (← getUnsolvedGoals).isEmpty then
        trace[ENNRealArith.real_computation] "Solved with ENNReal fallback"
        return
    catch _ => pure ()

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
