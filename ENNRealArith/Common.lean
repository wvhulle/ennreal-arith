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


-- =============================================
-- TEST UTILITIES
-- =============================================

/-!
## Common Test Utilities for ENNReal Arithmetic

This section provides common test patterns and helper lemmas used across all
ENNReal arithmetic tactic modules.

Note: The current implementation focuses on `ℕ` to `ENNReal` coercions, which is
the most common use case. Future generalizations could extend to other numeric
types like `ℚ≥0` or abstract semirings, but would require careful consideration
of the mathematical properties that make these tactics work.
-/

section IdentityTests

/-- Test zero as additive identity -/
def test_zero_additive_identity (a : ℕ) : Prop := (↑a : ENNReal) + 0 = ↑a

/-- Test one as multiplicative identity -/
def test_one_multiplicative_identity (a : ℕ) : Prop := (↑a : ENNReal) * 1 = ↑a

/-- Test division by one identity -/
def test_division_by_one_identity (a : ℕ) : Prop := (↑a : ENNReal) / 1 = ↑a

end IdentityTests

section ConcreteArithmetic

/-- Common concrete test numbers -/
def test_numbers : List ℕ := [2, 3, 5, 6, 7, 18]

/-- Test addition preservation for natural number casts -/
def test_addition_preserves_cast (a b : ℕ) : Prop := 
  (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ)

/-- Test multiplication preservation for natural number casts -/
def test_multiplication_preserves_cast (a b : ℕ) : Prop := 
  (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ)

end ConcreteArithmetic

section DivisionTests

/-- Test division by self for nonzero numbers -/
def test_division_by_self (a : ℕ) (_ : a ≠ 0) : Prop := 
  (↑a : ENNReal) / ↑a = 1

/-- Test zero division property -/
def test_zero_division (a : ℕ) : Prop := 
  (0 : ENNReal) / ↑a = 0

end DivisionTests

end ENNRealArith
