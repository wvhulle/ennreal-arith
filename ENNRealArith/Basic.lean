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

def MAX_LIFTING_PASSES : Nat := 10

/- The amount of atoms that should still be lifted by applying operator lifts. -/
partial def atoms_remaining_lift (e : Expr) : Nat :=
  let rec count (e : Expr) (acc : Nat) : Nat :=
    let acc' := if e.isAppOf ``ENNReal.ofReal then acc + 1 else acc
    e.getAppArgs.foldl (fun acc arg => count arg acc) acc'
  count e 0

def fullyLifted (e : Expr) : Bool :=
  e.isAppOf ``ENNReal.ofReal ||
  e.isAppOf ``OfNat.ofNat ||
  e.isAppOf ``Nat.cast ||
  e.isAppOf ``Top.top

def isReadyForFinalComputation (goalType : Expr) : Bool :=
  let args := goalType.getAppArgs
  args.size >= 3 && 
  [``Eq, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge].any (goalType.isAppOfArity · 3) &&
  fullyLifted args[1]! && fullyLifted args[2]!


structure FiniteExpr where
  expr : Expr
  proof : Expr



def contextDeclAssumesFiniteFVar (contextDecl : Expr) (maybeFiniteE : Expr) : Bool :=
  let top := Expr.const ``Top.top []
  let checkPair (lhs rhs : Expr) : Bool :=
    (lhs == maybeFiniteE && rhs == top) || (rhs == maybeFiniteE && lhs == top)

  match contextDecl with
  | .app (.app (.app (.const ``Ne _) _) lhs) rhs => checkPair lhs rhs
  | .app (.const ``Not _) (.app (.app (.app (.const ``Eq _) _) lhs) rhs) => checkPair lhs rhs
  | _ => false

def maybeFiniteFVar (e: Expr) : TacticM (Option FiniteExpr) := do
  if e.isFVar then
    let ctx ← getLCtx
    ctx.findDeclM? fun decl => do
      if decl.isImplementationDetail then
        return none
      if contextDeclAssumesFiniteFVar decl.type e then
        return some ⟨e, decl.toExpr⟩
      else
        return none
  else
    pure none

inductive ENNRealExpr
| finite_free_var: FiniteExpr → ENNRealExpr
| no_finite_free_var: Expr → ENNRealExpr

/- Search all the atomic expressions with values in the ENNReal numbers, both variables and literals. -/
partial def search_atoms (e : Expr) : TacticM (Array ENNRealExpr) := do
  let rec visit (expr : Expr) : TacticM (Array ENNRealExpr) := do
    match expr with
    | .app (.app (.app (.const ``OfNat.ofNat _) (.const ``ENNReal _)) (.lit _)) _
      | .app (.const ``ofNNReal _) _  =>
      return #[ENNRealExpr.no_finite_free_var expr]
    | fvar =>
      if fvar.isFVar then
        let finiteVar? ← maybeFiniteFVar fvar
        match finiteVar? with
        | some finiteExpr => return #[ENNRealExpr.finite_free_var finiteExpr]
        | none => return #[ENNRealExpr.no_finite_free_var fvar]
      else
        match fvar with
        | .app f a =>
          let leftAtoms ← visit f
          let rightAtoms ← visit a
          return leftAtoms ++ rightAtoms
        | _ => return #[]

  let allAtoms ← visit e

  -- Remove exact duplicates
  let mut uniqueAtoms := #[]
  for atom in allAtoms do
    let isDuplicate := uniqueAtoms.any (fun a => match (a, atom) with
      | (ENNRealExpr.no_finite_free_var e1, ENNRealExpr.no_finite_free_var e2) => e1.equal e2
      | (ENNRealExpr.finite_free_var f1, ENNRealExpr.finite_free_var f2) => f1.expr.equal f2.expr
      | _ => false)
    if !isDuplicate then
      uniqueAtoms := uniqueAtoms.push atom

  return uniqueAtoms


def lift_to_real (ennExpr : ENNRealExpr) : TacticM Unit := do
  match ennExpr with
  | .finite_free_var ⟨expr, proof⟩ =>
    trace[ENNRealArith.enn_conversion] m!"Converting free var {expr} with finiteness proof {proof} to a free var in the reals."
    let proofSyntax ← proof.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal $proofSyntax]))
  | .no_finite_free_var expr =>
    trace[ENNRealArith.enn_conversion] m!"Trying to prove that expression {expr} is finite using `norm_num` and converting to a real."
    let exprSyntax ← expr.toSyntax
    evalTactic (← `(tactic| rw [← ENNReal.ofReal_toReal (by norm_num : $exprSyntax ≠ ⊤)]))

def lift_atoms (goalType : Expr) : TacticM Unit := do
  let exprs ← search_atoms goalType
  trace[ENNRealArith.enn_conversion] m!"Found {exprs.size} ENNReal expressions to convert"

  for expr in exprs do
    try lift_to_real expr
    catch _ => continue

def ops_lifting_tactics : TacticM (Array (TSyntax `tactic)) :=
  return #[
    ← `(tactic| rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < _)]),
    ← `(tactic| rw [← ENNReal.ofReal_mul]),
    ← `(tactic| rw [← ENNReal.ofReal_add]),
    ← `(tactic| rw [← ENNReal.ofReal_one]),
    ← `(tactic| rw [← ENNReal.ofReal_zero])
  ]

def apply_op_lift_tactic (tactic : TSyntax `tactic) : TacticM Bool := do
  let goalBefore ← (← getMainGoal).getType
  let countBefore := atoms_remaining_lift goalBefore

  try
    evalTactic tactic

    let goalAfter ← (← getMainGoal).getType
    let countAfter := atoms_remaining_lift goalAfter

    trace[ENNRealArith.ofreal_lifting] m!"Lifting progress: {countBefore} → {countAfter} ofReal occurrences"

    return ↑(countAfter < countBefore)

  catch _ =>
    return false



def lift_operators : TacticM Unit := do
  trace[ENNRealArith.ofreal_lifting] m!"Starting ofReal lifting on: {← getMainGoal}"

  let liftingRules ← ops_lifting_tactics
  let mut previousGoalType : Option Expr := none

  for iteration in List.range MAX_LIFTING_PASSES do
    trace[ENNRealArith.ofreal_lifting] m!"Lifting iteration {iteration + 1}"
    let mut progress_current_iteration := false
    for rule in liftingRules do
      let progress_current_tactic ← apply_op_lift_tactic rule
      if progress_current_tactic then
        progress_current_iteration := true
    let currentType ← (← getMainGoal).getType
    if progress_current_iteration == false then
      trace[ENNRealArith.ofreal_lifting] m!"No progress made for goal {currentType}, stopping operator lifting iterations"
      break
    previousGoalType := some currentType

elab "eq_as_reals" : tactic =>
  withMainContext do
    let goalType ← whnf (← (← getMainGoal).getType)
    let initialGoalState ← saveState

    try
      evalTactic (← `(tactic| rfl))
    catch _ =>
      lift_atoms goalType
      lift_operators

      try
        evalTactic (← `(tactic|
        all_goals (first | congr 1 | apply ENNReal.toReal_nonneg) <;> norm_num))
        if (← getUnsolvedGoals).isEmpty then
          return
      catch _ => pure ()

      restoreState initialGoalState
      try
        evalTactic (← `(tactic| ring_nf))
        if (← getUnsolvedGoals).isEmpty then
          return
      catch _ => pure ()

      restoreState initialGoalState
      throwError "eq_as_reals failed: Could not prove the goal."
