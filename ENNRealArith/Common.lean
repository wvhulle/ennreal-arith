import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/-!
# Common Utilities for ENNReal Arithmetic Tactics

This file contains common imports and helper functions used across all ENNReal arithmetic tactics.
-/

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

/--
Helper function to try a sequence of tactics and return whether they solved all goals.
-/
def tryTacticSequence (tactics : List (TSyntax `tactic)) : TacticM Bool := do
  try
    for tac in tactics do evalTactic tac
    return (← getUnsolvedGoals).isEmpty
  catch _ => return false

/--
Helper function to try a single tactic and return whether it solved all goals.
-/
def tryTactic (tac : TSyntax `tactic) : TacticM Bool := do
  try
    let goals_before ← getUnsolvedGoals
    if goals_before.isEmpty then return true
    evalTactic tac
    let goals_after ← getUnsolvedGoals
    return goals_after.isEmpty
  catch _ => return false

/--
Standard simplification lemmas for ENNReal arithmetic operations.
Includes basic arithmetic identities, commutativity, associativity,
and ENNReal-specific lemmas for division and casting.
-/
def standardENNRealSimpLemmas : List Name := [
  `add_zero, `zero_add, `mul_one, `one_mul, `mul_zero, `zero_mul,
  `div_one, `one_div, `inv_inv, `mul_comm, `mul_assoc, `mul_left_comm,
  `ENNReal.div_eq_inv_mul, `ENNReal.zero_div, `Nat.cast_mul, `Nat.cast_zero, `Nat.cast_one
]

/--
Try basic computational tactics in order.
-/
def tryBasicComputation : TacticM Bool := do
  let basicTactics := [
    ← `(tactic| norm_num),
    ← `(tactic| norm_cast),
    ← `(tactic| rfl)
  ]
  for tac in basicTactics do
    if ← tryTactic tac then return true
  return false

/--
Common pattern for ENNReal arithmetic tactics - tries basic computation,
then simplification, then custom sequences.
-/
def tryStandardENNRealTactics : TacticM Bool := do
  -- Try basic computation first
  if ← tryBasicComputation then return true
  
  -- Try standard simp
  if ← tryTactic (← `(tactic| simp only [add_zero, zero_add, mul_one, one_mul, mul_zero, zero_mul, div_one])) then return true
  
  return false

/--
Helper for creating ENNReal tactic with standard error message.
-/
def createENNRealTactic (tacticName : String) (customLogic : TacticM Bool) : TacticM Unit := do
  if ← tryStandardENNRealTactics then return
  if ← customLogic then return
  throwError s!"{tacticName} could not solve the goal"


/-- Repeatedly apply a tactic while it makes progress -/
partial def repeatWhileProgress (tac : TSyntax `tactic) : TacticM Unit := do
  let before ← getMainTarget
  try evalTactic tac catch _ => return
  let after ← getMainTarget
  if before != after then repeatWhileProgress tac


end ENNRealArith
