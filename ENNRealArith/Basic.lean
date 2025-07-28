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
  registerTraceClass `ENNRealArith.expr_search
  registerTraceClass `ENNRealArith.enn_conversion
  registerTraceClass `ENNRealArith.ofreal_lifting
  registerTraceClass `ENNRealArith.debug
  registerTraceClass `ENNRealArith.real_computation


namespace ENNRealArith

partial def countOfRealOccurrences (e : Expr) : Nat :=
  let count := if e.isAppOf ``ENNReal.ofReal then 1 else 0
  count + e.getAppArgs.foldl (fun acc arg => acc + countOfRealOccurrences arg) 0

def fullyLifted (e : Expr) : Bool :=
  e.isAppOf ``ENNReal.ofReal ||
  (e.isAppOfArity ``OfNat.ofNat 3 && 
   let args := e.getAppArgs
   args.size >= 3 && args[0]!.isAppOf ``ENNReal && args[1]!.isLit) ||
  (e.isAppOfArity ``Nat.cast 2 && 
   let args := e.getAppArgs
   args.size >= 2 && args[0]!.isAppOf ``ENNReal && args[1]!.isLit)

def isReadyForFinalComputation (goalType : Expr) : Bool :=
  let relations := [``Eq, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge]
  relations.any (goalType.isAppOfArity · 3) &&
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
    if isFinitePattern e declType then 
      return some (FiniteVar.mk e decl.toExpr)
    else 
      return none
where
  isFinitePattern (e : Expr) (declType : Expr) : Bool :=
    (declType.isAppOfArity ``Ne 3 &&
     let args := declType.getAppArgs
     args.size >= 3 && args[1]! == e && args[2]!.isAppOfArity ``Top.top 2) ||
    (declType.isAppOfArity ``Not 1 &&
     let eqExpr := declType.getAppArgs[0]!
     eqExpr.isAppOfArity ``Eq 3 &&
     let args := eqExpr.getAppArgs
     args.size >= 3 && args[1]! == e && args[2]!.isAppOfArity ``Top.top 2)




inductive ENNRealExpr
| finite_var: FiniteVar → ENNRealExpr
| other: Expr → ENNRealExpr

partial def findENNVarExpr (e : Expr) : MetaM (Array ENNRealExpr) := do
  let mut literals := #[]

  if e.isFVar then
    try
      if let some finite_var <- maybeFiniteFVar e then
        literals := literals.push (ENNRealExpr.finite_var finite_var)
        trace[ENNRealArith.expr_search] m!"Found finite variable: {finite_var.expr}"
    catch _ => pure ()

  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args.size >= 3 && args[0]!.isAppOf ``ENNReal && args[1]!.isLit then
      literals := literals.push (ENNRealExpr.other e)
      trace[ENNRealArith.expr_search] m!"Found ENNReal literal: {e}"

  if e.isApp && e.getAppFn.constName? == some ``ofNNReal && e.getAppArgs.size >= 1 then
    literals := literals.push (ENNRealExpr.other e)
    trace[ENNRealArith.expr_search] m!"Found ofNNReal expression: {e}"

  try
    match e with
    | .app f a =>
      literals := literals ++ (← findENNVarExpr f) ++ (← findENNVarExpr a)
    | .lam _ _ b _ | .forallE _ _ b _ | .mdata _ b | .proj _ _ b => 
      literals := literals ++ (← findENNVarExpr b)
    | .letE _ _ _ _ _ =>
      let reducedExpr ← whnf e
      literals := literals ++ (← findENNVarExpr reducedExpr)
    | _ => pure ()
  catch _ => pure ()

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
    ← `(tactic| (rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)])),
    ← `(tactic| (rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)])),
    ← `(tactic| (rw [← ENNReal.ofReal_mul])),
    ← `(tactic| (rw [← ENNReal.ofReal_add])),
    ← `(tactic| (rw [← ENNReal.ofReal_one])),
    ← `(tactic| (rw [← ENNReal.ofReal_zero]))
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
  
  try
    evalTactic (← `(tactic|
      (first | congr 1 | rw [← ENNReal.toReal_lt_toReal_iff] | rw [← ENNReal.toReal_le_toReal_iff] | skip) <;>
      all_goals (first | apply ENNReal.toReal_nonneg | skip) <;>
      simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]))
    let goal ← getMainGoal
    trace[ENNRealArith.real_computation] m!"Real conversion successful: {goal}"
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real conversion failed: {e.toMessageData}"
  
  try
    let goal ← getMainGoal
    trace[ENNRealArith.real_computation] m!"Attempting norm_num on: {goal}"
    
    evalTactic (← `(tactic| all_goals (first | congr 1 ; norm_num | norm_num)))
    
    let remainingGoals ← getUnsolvedGoals
    if !remainingGoals.isEmpty then
      let goal ← getMainGoal
      trace[ENNRealArith.real_computation] m!"norm_num incomplete, trying ring_nf on: {goal}"
      evalTactic (← `(tactic| all_goals ring_nf))
    
    let finalGoals ← getUnsolvedGoals
    if finalGoals.isEmpty then
      trace[ENNRealArith.real_computation] "Successfully solved with real arithmetic"
      return
    
    restoreState initialGoalState
    throwError "eq_as_reals failed: Could not prove the goal using real arithmetic."
  catch e =>
    trace[ENNRealArith.real_computation] m!"Real arithmetic failed: {e.toMessageData}"
    try
      restoreState initialGoalState
      trace[ENNRealArith.real_computation] "Trying ENNReal algebraic fallback"
      evalTactic (← `(tactic| first | ac_rfl | ring_nf | skip))
      let goals ← getUnsolvedGoals
      if goals.isEmpty then 
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
