import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

import ENNRealArith.InvPatterns

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_fraction_add" : tactic


elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  try evalTactic (← `(tactic| rw [add_assoc])) catch _ => pure ()
  try evalTactic (← `(tactic| rw [add_zero])) catch _ => pure ()
  try evalTactic (← `(tactic| rw [zero_add])) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [inv_eq_one_div])) catch _ => pure ()
  let rec repeatAddDiv : TacticM Unit := do
    let before ← getMainTarget
    try evalTactic (← `(tactic| rw [<- ENNReal.add_div])) catch _ => pure ()
    let after ← getMainTarget
    if before != after then repeatAddDiv else pure ()
  repeatAddDiv
  try evalTactic (← `(tactic| ennreal_inv_patterns)) catch _ => pure ()
  if !(← getUnsolvedGoals).isEmpty then
    throwError "ennreal_fraction_add could not solve the goal"
end ENNRealArith

section TestSuite

lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_simplification : (3 : ENNReal) / 18 = 1 / 6 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_fraction_add

lemma test_inverse_and_fraction_addition : (18 : ENNReal)⁻¹ + 2 / 18 = 6⁻¹ := by
  ennreal_fraction_add

end TestSuite
