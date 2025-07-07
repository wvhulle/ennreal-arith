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

/-- Convert an ENNReal equation to a Real equation when both sides are not infinity -/
lemma ennreal_eq_via_toReal {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]

/-- Tactic to convert ENNReal equations to Real equations when possible -/
syntax "ennreal_to_real" : tactic

elab_rules : tactic | `(tactic| ennreal_to_real) => do
  evalTactic (← `(tactic| (
    have h_lhs : _ ≠ ⊤ := by first | norm_num | simp
    have h_rhs : _ ≠ ⊤ := by first | norm_num | simp
    rw [ENNRealArith.ennreal_eq_via_toReal h_lhs h_rhs]
  )))

syntax "ennreal_fraction_add" : tactic


elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  try evalTactic (← `(tactic| rw [add_assoc])) catch _ => pure ()
  try evalTactic (← `(tactic| rw [add_zero])) catch _ => pure ()
  try evalTactic (← `(tactic| rw [zero_add])) catch _ => pure ()
  try evalTactic (← `(tactic| simp only [inv_eq_one_div])) catch _ => pure ()
  
  -- First try the standard approach for same denominators
  let rec repeatAddDiv : TacticM Unit := do
    let before ← getMainTarget
    try evalTactic (← `(tactic| rw [<- ENNReal.add_div])) catch _ => pure ()
    let after ← getMainTarget
    if before != after then repeatAddDiv else pure ()
  repeatAddDiv

  try evalTactic (← `(tactic| ennreal_inv_patterns)) catch _ => pure ()

  -- If standard approach fails, try conversion to real for mixed denominators
  if !(← getUnsolvedGoals).isEmpty then
    try
      evalTactic (← `(tactic| (
        -- Convert to real numbers for mixed denominators
        rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]
        rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
        all_goals norm_num
      )))
    catch _ =>
      throwError "ennreal_fraction_add could not solve the goal"

end ENNRealArith

section TestSuite

lemma test_mixed_denominators_auto : (1 : ENNReal) / 18 + 1 / 9 + 0 = 1 / 6 := by
  ennreal_fraction_add

lemma test_mixed_denominators : (1 : ENNReal) / 18 + 1 / 9 + 0 = 1 / 6 := by
  rw [add_zero]
  rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
  all_goals norm_num






lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_simplification : (3 : ENNReal) / 18 = 1 / 6 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_fraction_add

lemma test_inverse_and_fraction_addition : (18 : ENNReal)⁻¹ + 2 / 18 = 6⁻¹ := by
  ennreal_fraction_add





end TestSuite
