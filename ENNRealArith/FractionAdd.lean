import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

import ENNRealArith.InvPatterns
import ENNRealArith.Common

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


syntax "ennreal_fraction_add" : tactic

/-- Simplify expressions of ENNReals that contain additions and fractions. -/
elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))

  repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

  let _ ← tryTactic (← `(tactic| ennreal_inv_patterns))

  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num),
    ]



end ENNRealArith

section TestSuite

lemma test_addition_then_division : ((1 : ENNReal) + 2) / 18 = 1 / 6 := by
  ennreal_fraction_add


lemma test_inverse_pattern_with_context (_h1 : True) (_h2 : 1 + 1 = 2) : (6 : ENNReal) * 18⁻¹ = 3⁻¹ := by
  ennreal_fraction_add


lemma test_mixed_denominators : (1 : ENNReal) / 18 + 1 / 9 + 0 = 1 / 6 := by
  ennreal_fraction_add


lemma complex_add_fractions: 18⁻¹ + 18⁻¹ + (2 / 18 + 2 / 18) + (2 / 18 + (18⁻¹ + 18⁻¹ + 2 / 18) + (2 / 18 + (2 / 18 + (18⁻¹ + 18⁻¹)))) = (1 : ENNReal ) := by
  ennreal_fraction_add

lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_simplification : (3 : ENNReal) / 18 = 1 / 6 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_fraction_add

lemma test_inverse_and_fraction_addition : (18 : ENNReal)⁻¹ + 2 / 18 = 6⁻¹ := by
  ennreal_fraction_add


end TestSuite
