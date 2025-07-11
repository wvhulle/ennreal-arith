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


def isConcreteDivisionGoal (target : Expr) : Bool :=
  target.isAppOfArity ``Eq 3 &&
  let lhs := target.getArg! 1
  let rhs := target.getArg! 2
  lhs.isAppOfArity ``HDiv.hDiv 6 &&
  (rhs.isAppOfArity ``OfNat.ofNat 3 && rhs.getArg! 1 == mkNatLit 1)

end ENNRealArith
