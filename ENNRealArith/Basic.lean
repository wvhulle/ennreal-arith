import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Expr
import Lean.PrettyPrinter
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Lean
import Lean.Util.Trace
import Std.Data.HashMap
import ENNRealArith.Properties

open Lean Meta Elab Tactic ENNReal Qq Std.HashMap

initialize
  -- Main trace classes
  registerTraceClass `ENNRealArith
  registerTraceClass `ENNRealArith.debug
  
  -- Expression analysis and caching-related traces
  registerTraceClass `ENNRealArith.atom_search
  registerTraceClass `ENNRealArith.atom_search.cache
  registerTraceClass `ENNRealArith.atom_search.performance
  
  -- Expression conversion and lifting traces  
  registerTraceClass `ENNRealArith.enn_conversion
  registerTraceClass `ENNRealArith.enn_conversion.cache
  registerTraceClass `ENNRealArith.ofreal_lifting
  registerTraceClass `ENNRealArith.ofreal_lifting.cache
  registerTraceClass `ENNRealArith.ofreal_lifting.performance
  
  -- Goal state and transformation traces
  registerTraceClass `ENNRealArith.goal_state
  registerTraceClass `ENNRealArith.goal_transformations
  
  -- Final computation and fallback traces
  registerTraceClass `ENNRealArith.real_computation
  registerTraceClass `ENNRealArith.real_computation.cache
  registerTraceClass `ENNRealArith.fallback_strategies
  
  -- Error handling and diagnostics
  registerTraceClass `ENNRealArith.error_handling
  registerTraceClass `ENNRealArith.performance_metrics


namespace ENNRealArith

def MAX_LIFTING_PASSES : Nat := 10

/- The amount of atoms that should still be lifted by applying operator lifts. -/
partial def atoms_remaining_lift (e : Expr) : Nat :=
  (if e.isAppOf ``ENNReal.ofReal then 1 else 0) +
  e.getAppArgs.foldl (· + atoms_remaining_lift ·) 0

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
  trace[ENNRealArith.atom_search] m!"Checking if expression {e} is a finite free variable"
  
  if e.isFVar then
    trace[ENNRealArith.atom_search] m!"Expression is a free variable, searching for finiteness proof"
    let ctx ← getLCtx
    let result ← ctx.findDeclM? fun decl => do
      if decl.isImplementationDetail then 
        trace[ENNRealArith.atom_search] m!"Skipping implementation detail declaration: {decl.userName}"
        return none
      
      trace[ENNRealArith.atom_search] m!"Checking declaration {decl.userName} with type {decl.type}"
      if contextDeclAssumesFiniteFVar decl.type e  then
        trace[ENNRealArith.atom_search] m!"Found finiteness proof for {e} in declaration {decl.userName}"
        return some ⟨e, decl.toExpr ⟩
      else
        trace[ENNRealArith.atom_search] m!"Declaration {decl.userName} does not provide finiteness for {e}"
        return none
    
    match result with
    | some finite_expr => 
      trace[ENNRealArith.atom_search.cache] m!"Successfully cached finiteness proof for variable {e}"
      return result
    | none => 
      trace[ENNRealArith.atom_search] m!"No finiteness proof found for free variable {e}"
      return none
  else
    trace[ENNRealArith.atom_search] m!"Expression {e} is not a free variable"
    pure none

inductive ENNRealExpr
| finite_free_var: FiniteExpr → ENNRealExpr
| no_finite_free_var: Expr → ENNRealExpr

/- Search all the atomic expressions with values in the ENNReal numbers, both variables and literals. -/
partial def search_atoms (e : Expr) : MetaM (Array ENNRealExpr) := do
  trace[ENNRealArith.atom_search] m!"Starting atom search in expression: {e}"
  let startTime ← IO.monoMsNow
  let mut atoms := #[]
  let mut visitedExprs : HashMap Expr Unit := {}
  
  let rec searchImpl (expr : Expr) : MetaM Unit := do
    -- Cache hit detection
    if visitedExprs.contains expr then
      trace[ENNRealArith.atom_search.cache] m!"Cache hit: skipping already visited expression {expr}"
      return
    
    visitedExprs := visitedExprs.insert expr ()
    trace[ENNRealArith.atom_search] m!"Analyzing expression: {expr}"
    
    match expr with
    | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``ENNReal _)) (.lit _)) _
      | .app (.const ``ofNNReal _) _  =>
      trace[ENNRealArith.atom_search] m!"Found ENNReal atom: {expr}"
      atoms := atoms.push (ENNRealExpr.no_finite_free_var expr)
    | .app f a => 
      trace[ENNRealArith.atom_search] m!"Recursing into application: f={f}, a={a}"
      searchImpl f
      searchImpl a
    | _ => 
      trace[ENNRealArith.atom_search] m!"No match for expression type: {expr}"
      pure ()

  searchImpl e
  
  let endTime ← IO.monoMsNow
  let duration := endTime - startTime
  trace[ENNRealArith.atom_search.performance] m!"Atom search completed in {duration}ms, found {atoms.size} atoms, visited {visitedExprs.size} expressions"
  trace[ENNRealArith.atom_search.cache] m!"Cache statistics: {visitedExprs.size} unique expressions processed"
  
  return atoms


def lift_to_real (ennExpr : ENNRealExpr) : TacticM Unit := do
  match ennExpr with
  | .finite_free_var ⟨expr, proof⟩ =>
    trace[ENNRealArith.enn_conversion] m!"Converting free var {expr} with finiteness proof {proof} to a free var in the reals."
    trace[ENNRealArith.enn_conversion.cache] m!"Using cached finiteness proof for variable conversion"
    let proofSyntax ← proof.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal $proofSyntax]))
  | .no_finite_free_var expr =>
    trace[ENNRealArith.enn_conversion] m!"Trying to prove that expression {expr} is finite using `norm_num` and converting to a real."
    let exprSyntax ← expr.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $exprSyntax ≠ ⊤)]))

def lift_atoms (goalType : Expr) : TacticM Unit := do
  trace[ENNRealArith.enn_conversion] m!"Starting atom lifting for goal: {goalType}"
  let startTime ← IO.monoMsNow
  
  let exprs ← search_atoms goalType
  trace[ENNRealArith.enn_conversion] m!"Found {exprs.size} ENNReal expressions to convert"
  trace[ENNRealArith.enn_conversion.cache] m!"Expression cache populated with {exprs.size} entries"

  let mut successful_lifts := 0
  let mut failed_lifts := 0
  
  for expr in exprs do
    trace[ENNRealArith.enn_conversion] m!"Attempting to lift expression: {expr}"
    try 
      lift_to_real expr
      successful_lifts := successful_lifts + 1
      trace[ENNRealArith.enn_conversion] m!"Successfully lifted expression {expr}"
    catch e => 
      failed_lifts := failed_lifts + 1
      trace[ENNRealArith.enn_conversion] m!"Failed to lift expression {expr}: {e.toMessageData}"
      trace[ENNRealArith.error_handling] m!"Conversion error for {expr}: {e.toMessageData}"
      continue
  
  let endTime ← IO.monoMsNow
  let duration := endTime - startTime
  trace[ENNRealArith.enn_conversion.performance] m!"Atom lifting completed in {duration}ms"
  trace[ENNRealArith.enn_conversion.cache] m!"Lift statistics: {successful_lifts} successful, {failed_lifts} failed"
  trace[ENNRealArith.performance_metrics] m!"Conversion efficiency: {successful_lifts * 100 / (successful_lifts + failed_lifts)}% success rate"

def ops_lifting_tactics : TacticM (Array (TSyntax `tactic)) := do
  return #[
    ← `(tactic| rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_mul]),
    ← `(tactic| rw [← ENNReal.ofReal_add]),
    ← `(tactic| rw [← ENNReal.ofReal_one]),
    ← `(tactic| rw [← ENNReal.ofReal_zero])
  ]

def apply_op_lift_tactic (tactic : TSyntax `tactic) : TacticM Bool := do
  trace[ENNRealArith.ofreal_lifting] m!"Applying operator lifting tactic: {tactic}"
  let goalBefore ← (← getMainGoal).getType
  let countBefore := atoms_remaining_lift goalBefore
  
  trace[ENNRealArith.ofreal_lifting.cache] m!"Pre-tactic state: {countBefore} atoms remaining to lift"
  trace[ENNRealArith.goal_state] m!"Goal before tactic: {goalBefore}"

  try
    let tacticStartTime ← IO.monoMsNow
    evalTactic tactic
    let tacticEndTime ← IO.monoMsNow
    let tacticDuration := tacticEndTime - tacticStartTime

    let goalAfter ← (← getMainGoal).getType
    let countAfter := atoms_remaining_lift goalAfter
    let progress := countAfter < countBefore

    trace[ENNRealArith.ofreal_lifting] m!"Lifting progress: {countBefore} → {countAfter} ofReal occurrences"
    trace[ENNRealArith.ofreal_lifting.cache] m!"Cache efficiency: {if progress then "IMPROVED" else "NO_CHANGE"}"
    trace[ENNRealArith.ofreal_lifting.performance] m!"Tactic execution time: {tacticDuration}ms"
    trace[ENNRealArith.goal_transformations] m!"Goal transformation: {goalBefore} → {goalAfter}"
    
    if progress then
      trace[ENNRealArith.ofreal_lifting.cache] m!"Successful lift reduced complexity by {countBefore - countAfter} atoms"
    else
      trace[ENNRealArith.ofreal_lifting.cache] m!"No progress made - potential cache staleness or tactic mismatch"

    return ↑progress

  catch e =>
    trace[ENNRealArith.ofreal_lifting] m!"Tactic failed: {e.toMessageData}"
    trace[ENNRealArith.error_handling] m!"Operator lifting tactic error: {e.toMessageData}"
    trace[ENNRealArith.ofreal_lifting.cache] m!"Tactic failure - no cache update performed"
    return false



def lift_operators : TacticM Unit := do
  trace[ENNRealArith.ofreal_lifting] m!"Starting ofReal lifting on: {← getMainGoal}"
  let initialGoalType ← (← getMainGoal).getType
  let initialAtomCount := atoms_remaining_lift initialGoalType
  trace[ENNRealArith.ofreal_lifting.cache] m!"Initial goal complexity: {initialAtomCount} atoms to lift"

  let liftingRules ← ops_lifting_tactics
  let mut previousGoalType : Option Expr := none
  let mut totalProgress := 0
  let startTime ← IO.monoMsNow

  for iteration in List.range MAX_LIFTING_PASSES do
    trace[ENNRealArith.ofreal_lifting] m!"Lifting iteration {iteration + 1}/{MAX_LIFTING_PASSES}"
    let iterationStartTime ← IO.monoMsNow
    let mut progress_current_iteration := false
    let mut rulesApplied := 0
    
    for rule in liftingRules do
      trace[ENNRealArith.ofreal_lifting] m!"Trying lifting rule in iteration {iteration + 1}: {rule}"
      let progress_current_tactic ← apply_op_lift_tactic rule
      if progress_current_tactic then
        progress_current_iteration := true
        rulesApplied := rulesApplied + 1
        totalProgress := totalProgress + 1
        trace[ENNRealArith.ofreal_lifting.cache] m!"Rule succeeded, total progress: {totalProgress}"
    
    let currentType ← (← getMainGoal).getType
    let currentAtomCount := atoms_remaining_lift currentType
    let iterationEndTime ← IO.monoMsNow
    let iterationDuration := iterationEndTime - iterationStartTime
    
    trace[ENNRealArith.ofreal_lifting.performance] m!"Iteration {iteration + 1} completed in {iterationDuration}ms, applied {rulesApplied} rules"
    trace[ENNRealArith.goal_state] m!"Goal state after iteration {iteration + 1}: {currentAtomCount} atoms remaining"
    
    if progress_current_iteration == false then
      trace[ENNRealArith.ofreal_lifting] m!"No progress made for goal {currentType}, stopping operator lifting iterations"
      trace[ENNRealArith.ofreal_lifting.cache] m!"Lifting convergence reached at iteration {iteration + 1}"
      break
    
    -- Detect potential infinite loops or cache issues
    if let some prevType := previousGoalType then
      if prevType == currentType then
        trace[ENNRealArith.ofreal_lifting.cache] m!"WARNING: Goal state unchanged despite reported progress - potential cache inconsistency"
        trace[ENNRealArith.error_handling] m!"Potential cache bug detected: progress reported but no goal change"
    
    previousGoalType := some currentType

  let endTime ← IO.monoMsNow
  let totalDuration := endTime - startTime
  let finalAtomCount := atoms_remaining_lift (← (← getMainGoal).getType)
  let atomsReduced := initialAtomCount - finalAtomCount
  
  trace[ENNRealArith.ofreal_lifting.performance] m!"Total lifting completed in {totalDuration}ms"
  trace[ENNRealArith.performance_metrics] m!"Lifting summary: {atomsReduced} atoms reduced, {totalProgress} successful rule applications"
  trace[ENNRealArith.ofreal_lifting.cache] m!"Cache performance: reduced complexity from {initialAtomCount} to {finalAtomCount} atoms"


def solveWithRealArithmetic : TacticM Unit := do
  trace[ENNRealArith.real_computation] "Starting real arithmetic solver"
  let startTime ← IO.monoMsNow
  
  evalTactic (← `(tactic| all_goals norm_num))

  if !(← getUnsolvedGoals).isEmpty then
    let normNumTime ← IO.monoMsNow
    let normNumDuration := normNumTime - startTime
    trace[ENNRealArith.real_computation] "norm_num incomplete, trying ring_nf"
    trace[ENNRealArith.real_computation.performance] m!"norm_num completed in {normNumDuration}ms, proceeding to ring_nf"
    trace[ENNRealArith.fallback_strategies] "Falling back to ring normalization"
    
    evalTactic (← `(tactic| all_goals ring_nf))
    
    let endTime ← IO.monoMsNow
    let totalDuration := endTime - startTime
    let ringNfDuration := endTime - normNumTime
    trace[ENNRealArith.real_computation.performance] m!"ring_nf completed in {ringNfDuration}ms (total: {totalDuration}ms)"
  else
    let endTime ← IO.monoMsNow
    let totalDuration := endTime - startTime
    trace[ENNRealArith.real_computation.performance] m!"norm_num solved goal in {totalDuration}ms"
    trace[ENNRealArith.real_computation.cache] "norm_num cache hit - efficient solution"

def reduce (initialGoalState : Tactic.SavedState) : TacticM Unit := do
  trace[ENNRealArith.real_computation] "Converting ENNReal goal to Real arithmetic"
  let startTime ← IO.monoMsNow
  let goalType ← (← getMainGoal).getType
  
  trace[ENNRealArith.goal_state] m!"Starting reduction with goal: {goalType}"
  trace[ENNRealArith.real_computation.cache] "Attempting real arithmetic approach"

  -- Try real arithmetic approach
  try
    let realArithStartTime ← IO.monoMsNow
    evalTactic (← `(tactic|
    all_goals (first | congr 1 | apply ENNReal.toReal_nonneg) <;> norm_num))
    let realArithEndTime ← IO.monoMsNow
    let realArithDuration := realArithEndTime - realArithStartTime
    
    if (← getUnsolvedGoals).isEmpty then
      let totalDuration := realArithEndTime - startTime
      trace[ENNRealArith.real_computation] "Successfully solved with real arithmetic"
      trace[ENNRealArith.real_computation.performance] m!"Real arithmetic solved in {realArithDuration}ms (total: {totalDuration}ms)"
      trace[ENNRealArith.real_computation.cache] "Real arithmetic cache hit - primary strategy successful"
      return
  catch e => 
    trace[ENNRealArith.real_computation] m!"Real arithmetic approach failed: {e.toMessageData}"
    trace[ENNRealArith.fallback_strategies] "Real arithmetic failed, trying ENNReal ring normalization"
    trace[ENNRealArith.error_handling] m!"Real arithmetic error: {e.toMessageData}"

  -- Try ENNReal ring normalization
  restoreState initialGoalState
  trace[ENNRealArith.goal_state] "State restored for fallback strategy"
  
  try
    let fallbackStartTime ← IO.monoMsNow
    evalTactic (← `(tactic| ring_nf))
    let fallbackEndTime ← IO.monoMsNow
    let fallbackDuration := fallbackEndTime - fallbackStartTime
    
    if (← getUnsolvedGoals).isEmpty then
      let totalDuration := fallbackEndTime - startTime
      trace[ENNRealArith.real_computation] "Solved with ENNReal fallback"
      trace[ENNRealArith.fallback_strategies] m!"ENNReal ring normalization succeeded in {fallbackDuration}ms"
      trace[ENNRealArith.real_computation.cache] "Fallback strategy cache hit - secondary method successful"
      trace[ENNRealArith.performance_metrics] m!"Total time including fallback: {totalDuration}ms"
      return
  catch e => 
    trace[ENNRealArith.fallback_strategies] m!"ENNReal fallback also failed: {e.toMessageData}"
    trace[ENNRealArith.error_handling] m!"All strategies exhausted, final error: {e.toMessageData}"

  restoreState initialGoalState
  let finalDuration := (← IO.monoMsNow) - startTime
  trace[ENNRealArith.performance_metrics] m!"Total failed attempt duration: {finalDuration}ms"
  trace[ENNRealArith.error_handling] "All reduction strategies failed"
  throwError "eq_as_reals failed: Could not prove the goal."

elab "eq_as_reals" : tactic =>
  withMainContext do
    let tacticStartTime ← IO.monoMsNow
    let goalType ← whnf (← (← getMainGoal).getType)
    let initialGoalState ← saveState
    
    trace[ENNRealArith] m!"eq_as_reals tactic started with goal: {goalType}"
    trace[ENNRealArith.goal_state] m!"Initial goal state saved"
    trace[ENNRealArith.performance_metrics] "Beginning tactic execution timing"

    -- Quick check for trivial case
    try
      trace[ENNRealArith] "Attempting quick reflexivity check"
      evalTactic (← `(tactic| rfl))
      let quickDuration := (← IO.monoMsNow) - tacticStartTime
      trace[ENNRealArith] "Goal solved by reflexivity"
      trace[ENNRealArith.performance_metrics] m!"Quick solve completed in {quickDuration}ms"
      trace[ENNRealArith.real_computation.cache] "Trivial case cache hit - no complex processing needed"
    catch _ =>
      trace[ENNRealArith] "Reflexivity failed, proceeding with full conversion process"
      trace[ENNRealArith.goal_transformations] "Starting comprehensive goal transformation"
      
      let conversionStartTime ← IO.monoMsNow
      lift_atoms goalType
      let conversionEndTime ← IO.monoMsNow
      let conversionDuration := conversionEndTime - conversionStartTime
      
      trace[ENNRealArith.performance_metrics] m!"Atom lifting phase completed in {conversionDuration}ms"
      
      let liftingStartTime ← IO.monoMsNow  
      lift_operators
      let liftingEndTime ← IO.monoMsNow
      let liftingDuration := liftingEndTime - liftingStartTime
      
      trace[ENNRealArith.performance_metrics] m!"Operator lifting phase completed in {liftingDuration}ms"
      
      let reductionStartTime ← IO.monoMsNow
      reduce initialGoalState
      let reductionEndTime ← IO.monoMsNow
      let reductionDuration := reductionEndTime - reductionStartTime
      
      let totalDuration := reductionEndTime - tacticStartTime
      trace[ENNRealArith.performance_metrics] m!"Final reduction phase completed in {reductionDuration}ms"
      trace[ENNRealArith.performance_metrics] m!"Total eq_as_reals execution time: {totalDuration}ms"
      trace[ENNRealArith] "eq_as_reals tactic completed successfully"
