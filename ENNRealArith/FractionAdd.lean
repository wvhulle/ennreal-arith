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


lemma test_fraction_add_manual : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  calc
    _ = ((1 : ENNReal) + (2 : ENNReal)) / (18: ENNReal):= by
      rw [<- ENNReal.add_div]
    _ = ( 1 + 2 ) / 18 := by
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num
    _ = 3 / 18 := by
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num

lemma test_fraction_add : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_simplify_manual : (3 : ENNReal) / 18 = 1 / 6 := by
  rw [ENNReal.div_eq_div_iff]
  all_goals norm_num

lemma test_fraction_simplify : (3 : ENNReal) / 18 = 1 / 6 := by
  ennreal_fraction_add

lemma test_complex_add_manual : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  calc
    _ =(1 : ENNReal) / 18 + 2 / 18 := by
      rw [add_zero]
    _ = 3 / 18 := by rw [test_fraction_add_manual]
    _ = 1 / 6 := by
      exact test_fraction_simplify_manual


lemma test_complex_add : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_fraction_add

lemma test_inverse_add_manual : (18 : ENNReal)⁻¹ + 2 / 18 = 6⁻¹ := by
  simp only [inv_eq_one_div]
  rw [test_fraction_add_manual]
  exact test_fraction_simplify_manual


lemma test_inverse_add : (18 : ENNReal)⁻¹ + 2 / 18 = 6⁻¹ := by
  ennreal_fraction_add

end TestSuite
