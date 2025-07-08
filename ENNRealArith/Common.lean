import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Helper function to try various ways of proving a natural number is nonzero.
Used by multiple tactics that need to establish nonzero conditions.
-/
def tryNonzeroProof : TacticM Unit := do
  try
    evalTactic (← `(tactic| assumption))
  catch _ =>
    try
      evalTactic (← `(tactic| apply ne_of_gt; assumption))
    catch _ =>
      try
        evalTactic (← `(tactic| norm_num))
      catch _ =>
        try
          evalTactic (← `(tactic| exact Nat.succ_ne_zero _))
        catch _ =>
          throwError "Could not prove nonzero condition"

def tryTacticSequence (tactics : List (TSyntax `tactic)) : TacticM Bool := do
  try
    for tac in tactics do evalTactic tac
    return (← getUnsolvedGoals).isEmpty
  catch _ => return false

def tryTactic (tac : TSyntax `tactic) : TacticM Bool := do
  try
    let goals_before ← getUnsolvedGoals
    if goals_before.isEmpty then return true
    evalTactic tac
    let goals_after ← getUnsolvedGoals
    return goals_after.isEmpty
  catch _ => return false

def tryBasicComputation : TacticM Bool := do
  let basicTactics := [
    ← `(tactic| norm_num),
    ← `(tactic| norm_cast),
    ← `(tactic| rfl)
  ]
  for tac in basicTactics do
    if ← tryTactic tac then return true
  return false

partial def repeatWhileProgress (tac : TSyntax `tactic) : TacticM Unit := do
  let before ← getMainTarget
  try evalTactic tac catch _ => return
  let after ← getMainTarget
  if before != after then repeatWhileProgress tac

structure GoalPattern where
  hasAddition : Bool
  hasMultiplication : Bool
  hasDivision : Bool
  hasInverse : Bool
  hasDoubleInverse : Bool
  hasMultiplicationInDivision : Bool
  isConcreteDivisionByOne : Bool
  isSimpleArithmetic : Bool

def analyzeExpr (e : Expr) : GoalPattern :=
  let hasAddition := e.find? (fun e => e.isAppOfArity ``HAdd.hAdd 6) |>.isSome
  let hasMultiplication := e.find? (fun e => e.isAppOfArity ``HMul.hMul 6) |>.isSome
  let hasDivision := e.find? (fun e => e.isAppOfArity ``HDiv.hDiv 6) |>.isSome
  let hasInverse := e.find? (fun e => e.isAppOfArity ``Inv.inv 3) |>.isSome
  let hasDoubleInverse := e.find? (fun e =>
    e.isAppOfArity ``Inv.inv 3 &&
    (e.getArg! 2).isAppOfArity ``Inv.inv 3
  ) |>.isSome
  let hasMultiplicationInDivision := e.find? (fun e =>
    e.isAppOfArity ``HMul.hMul 6 &&
    ((e.getArg! 4).isAppOfArity ``HDiv.hDiv 6 ||
     (e.getArg! 5).isAppOfArity ``HDiv.hDiv 6)
  ) |>.isSome
  let isConcreteDivisionByOne := e.isAppOfArity ``HDiv.hDiv 6 &&
    let num := e.getArg! 4
    let den := e.getArg! 5
    num == den
  let isSimpleArithmetic := !hasDivision && !hasInverse && (hasAddition || hasMultiplication)

  { hasAddition, hasMultiplication, hasDivision, hasInverse, hasDoubleInverse,
    hasMultiplicationInDivision, isConcreteDivisionByOne, isSimpleArithmetic }

def analyzeEqualityGoal (target : Expr) : MetaM (Option (GoalPattern × GoalPattern)) := do
  if !target.isAppOfArity ``Eq 3 then
    return none

  let lhs := target.getArg! 1
  let rhs := target.getArg! 2

  return some (analyzeExpr lhs, analyzeExpr rhs)

def isConcreteDivisionGoal (target : Expr) : Bool :=
  target.isAppOfArity ``Eq 3 &&
  let lhs := target.getArg! 1
  let rhs := target.getArg! 2
  lhs.isAppOfArity ``HDiv.hDiv 6 &&
  (rhs.isAppOfArity ``OfNat.ofNat 3 && rhs.getArg! 1 == mkNatLit 1)

end ENNRealArith
