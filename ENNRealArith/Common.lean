import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Qq

open Lean Meta Elab Tactic
open ENNReal Qq

namespace ENNRealArith



def tryNonzeroProof : TacticM Unit := do
  evalTactic (← `(tactic| first | assumption | norm_num))


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


/--
Detects concrete division goals of the form `a / b = 1` using QQ pattern matching.
Returns true if the goal represents a concrete division that equals 1.
-/
def isConcreteDivisionGoal (target : Expr) : MetaM Bool := do
  -- Check that we have a Prop goal first
  let targetType ← inferType target
  unless ← isDefEq targetType q(Prop) do
    return false

  -- Use QQ pattern matching on the target
  have targetQ : Q(Prop) := target
  match targetQ with
  | ~q(($a : ENNReal) / $b = 1) => return true
  | ~q((↑$na : ENNReal) / (↑$nb : ENNReal) = 1) => return true
  | _ => return false

end ENNRealArith
