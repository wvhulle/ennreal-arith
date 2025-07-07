import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

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
  -- First try basic simplifications
  if ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div])) then return

  -- Try to combine fractions with same denominator
  repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

  -- Try inverse and basic multiplication patterns
  if ← tryTactic (← `(tactic| simp only [inv_eq_one_div, mul_one, one_mul, inv_inv, mul_comm, mul_assoc, div_eq_mul_inv])) then return

  -- Try division simplification
  if ← tryTactic (← `(tactic| simp only [ENNReal.div_eq_div_iff] <;> norm_num)) then return

  -- Try norm_num for simple arithmetic
  if ← tryTactic (← `(tactic| norm_num)) then return

  -- Try converting to real numbers when finite
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num),
    ]



end ENNRealArith

section TestSuite

lemma test_addition_then_division : ((1 : ENNReal) + 2) / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 3 / 18 := by
  ennreal_fraction_add

lemma test_basic_arithmetic : (2 : ENNReal) + 3 = 5 := by
  ennreal_fraction_add

lemma test_zero_addition : (1 : ENNReal) / 6 + 0 = 1 / 6 := by
  ennreal_fraction_add

end TestSuite
