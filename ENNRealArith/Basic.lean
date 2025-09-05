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


structure FiniteExpr where
  expr : Expr
  proof : Expr



def contextDeclAssumesFiniteFVar (contextDecl : Expr) (maybeFiniteE : Expr)  : Bool :=
  let t := Expr.const ``Top.top []
  match contextDecl with
  -- lhs ≠ ⊤
  | .app ( .app ( .app (.const ``Ne _) _) lhs) rhs => (lhs == maybeFiniteE  && rhs == t) || (rhs == maybeFiniteE && lhs == maybeFiniteE)
  -- ¬ ( lhs = ⊤ )
  | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) _) lhs) rhs) => (lhs == maybeFiniteE  && rhs == t) || (rhs == maybeFiniteE && lhs == maybeFiniteE)
  | _ => false


def maybeFiniteFVar (e: Expr) : TacticM (Option FiniteExpr ) := do
  if e.isFVar then
    let ctx ← getLCtx
    ctx.findDeclM? fun decl => do
    if decl.isImplementationDetail then return none
      if contextDeclAssumesFiniteFVar decl.type e  then
        return some ⟨e, decl.toExpr ⟩
      else
        return none
  else
    pure none

inductive ENNRealExpr
| finite_free_var: FiniteExpr → ENNRealExpr
| no_finite_free_var: Expr → ENNRealExpr

partial def findENNVarExpr (e : Expr) : MetaM (Array ENNRealExpr) := do
  let mut literals := #[]
  match e with
  | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``ENNReal _)) (.lit _)) _ |
    .app (.const ``ofNNReal _) _ =>
    literals := literals.push (ENNRealExpr.no_finite_free_var e)
  | .app f a => literals := literals ++ (← findENNVarExpr f) ++ (← findENNVarExpr a)
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

def convertENNExpr (ennExpr : ENNRealExpr) : TacticM Unit := do
  match ennExpr with
  | .finite_free_var ⟨expr, proof⟩ =>
    trace[ENNRealArith.enn_conversion] m!"Converting finite var {expr} with proof {proof}"
    let proofSyntax ← proof.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal $proofSyntax]))
  | .no_finite_free_var expr =>
    trace[ENNRealArith.enn_conversion] m!"Converting literal {expr} with norm_num"
    let exprSyntax ← expr.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $exprSyntax ≠ ⊤)]))

def processENNExpressions (goalType : Expr) : TacticM Unit := do
  let ennExpressions ← findENNVarExpr goalType
  trace[ENNRealArith.enn_conversion] m!"Found {ennExpressions.size} ENNReal expressions to convert"

  for ennExpr in ennExpressions do
    try convertENNExpr ennExpr
    catch _ => continue

def getLiftingRules : TacticM (Array (TSyntax `tactic)) := do
  return #[
    ← `(tactic| rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_mul]),
    ← `(tactic| rw [← ENNReal.ofReal_add]),
    ← `(tactic| rw [← ENNReal.ofReal_one]),
    ← `(tactic| rw [← ENNReal.ofReal_zero])
  ]

def tryLiftingRule (rule : TSyntax `tactic) : TacticM Bool := do
  let goalBefore ← (← getMainGoal).getType
  let countBefore := countOfRealOccurrences goalBefore

  try
    evalTactic rule
    try evalTactic (← `(tactic| simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))
    catch _ => pure ()

    let goalAfter ← (← getMainGoal).getType
    let countAfter := countOfRealOccurrences goalAfter

    if countAfter < countBefore then
      trace[ENNRealArith.ofreal_lifting] m!"Lifting progress: {countBefore} → {countAfter} ofReal occurrences"

    return (countAfter < countBefore || isReadyForFinalComputation goalAfter)
  catch _ =>
    return false

def runLiftingPhases : TacticM Unit := do
  trace[ENNRealArith.ofreal_lifting] m!"Starting ofReal lifting on: {← getMainGoal}"

  let liftingRules ← getLiftingRules
  let mut previousGoalType : Option Expr := none

  for iteration in List.range 10 do
    trace[ENNRealArith.ofreal_lifting] m!"Lifting iteration {iteration + 1}"

    let mut madeProgress := false
    for rule in liftingRules do
      if ← tryLiftingRule rule then
        madeProgress := true
        if isReadyForFinalComputation (← (← getMainGoal).getType) then
          trace[ENNRealArith.ofreal_lifting] "Goal ready for final computation"
          return

    let currentType ← (← getMainGoal).getType
    if some currentType == previousGoalType || !madeProgress then
      trace[ENNRealArith.ofreal_lifting] "No progress made, stopping iterations"
      break
    previousGoalType := some currentType

def convertToRealArithmetic : TacticM Unit := do
  evalTactic (← `(tactic|
    (first | congr 1 | rw [← ENNReal.toReal_lt_toReal_iff] | rw [← ENNReal.toReal_le_toReal_iff] | skip) <;>
    all_goals (first | apply ENNReal.toReal_nonneg | skip) <;>
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))

def solveWithRealArithmetic : TacticM Unit := do
  evalTactic (← `(tactic| all_goals (first | congr 1 ; norm_num | norm_num)))

  if !(← getUnsolvedGoals).isEmpty then
    trace[ENNRealArith.real_computation] "norm_num incomplete, trying ring_nf"
    evalTactic (← `(tactic| all_goals ring_nf))

def tryENNRealFallback : TacticM Unit := do
  trace[ENNRealArith.real_computation] "Trying ENNReal algebraic fallback"
  evalTactic (← `(tactic| first | ac_rfl | ring_nf | skip))

def runFinalComputation (initialGoalState : Tactic.SavedState) : TacticM Unit := do
  trace[ENNRealArith.real_computation] "Converting ENNReal goal to Real arithmetic"

  try
    convertToRealArithmetic
    trace[ENNRealArith.real_computation] m!"Real conversion successful: {← getMainGoal}"
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real conversion failed: {e.toMessageData}"

  try
    trace[ENNRealArith.real_computation] m!"Attempting norm_num on: {← getMainGoal}"
    solveWithRealArithmetic

    if (← getUnsolvedGoals).isEmpty then
      trace[ENNRealArith.real_computation] "Successfully solved with real arithmetic"
      return

    restoreState initialGoalState
    throwError "eq_as_reals failed: Could not prove the goal using real arithmetic."
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real arithmetic failed: {e.toMessageData}"
    try
      restoreState initialGoalState
      tryENNRealFallback
      if (← getUnsolvedGoals).isEmpty then
        trace[ENNRealArith.real_computation] "Solved with ENNReal fallback"
        return
    catch _ => pure ()

    restoreState initialGoalState
    throwError "eq_as_reals failed: Could not prove the goal."

elab "eq_as_reals" : tactic =>
  withMainContext do
    let goalType ← whnf (← (← getMainGoal).getType)
    let initialGoalState ← saveState

    if ← tryReflexiveGoal goalType then return

    processENNExpressions goalType
    runLiftingPhases
    runFinalComputation initialGoalState
