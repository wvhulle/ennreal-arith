import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

import ENNRealArith.Common
import ENNRealArith.ArithmeticCore

set_option linter.docPrime false

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/-!
# ENNReal Fraction Operations

This module contains tactics for advanced fraction and inverse operations:
- Multiplication/division associativity (`ennreal_mul_div_assoc`)
- Inverse pattern transformations (`ennreal_inv_transform`)
- Fraction addition and simplification (`ennreal_fraction_add`)

These handle more complex ENNReal expressions involving fractions, inverses, and mixed operations.
-/

-- =============================================
-- MULTIPLICATION/DIVISION ASSOCIATIVITY TACTIC
-- =============================================

syntax "ennreal_mul_div_assoc" : tactic

/--
Tactic for proving ENNReal multiplication-division associativity.
Handles goals of the form `(↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal)`.
-/
elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do

    evalTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div,  one_mul, mul_one, Nat.cast_mul]))
    if (← getUnsolvedGoals).isEmpty then return

    evalTactic (← `(tactic| apply ENNReal.div_self))
    evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
    evalTactic (← `(tactic| assumption))
    evalTactic (← `(tactic| exact ENNReal.coe_ne_top))

    if (← getUnsolvedGoals).isEmpty then return

    throwError "ennreal_mul_div_assoc could not solve the goal"

-- =============================================
-- INVERSE PATTERN TRANSFORMATION TACTIC
-- =============================================

syntax "ennreal_inv_transform" : tactic

/--
Tactic for transforming ENNReal inverse and division expressions.
Handles complex transformations involving inverses, divisions, and multiplications.
Converts between forms like `a⁻¹ * b = b / a` and `(a⁻¹)⁻¹ = a`.
-/
elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    -- Try basic reflexivity first
    if ← tryTactic (← `(tactic| rfl)) then return

    -- Try a comprehensive simp with common inverse/division lemmas
    if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                           div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul])) then return

    let tactics : Array (TSyntax `tactic) := #[
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [mul_one]),
      ← `(tactic| rw [one_mul]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| (simp only [ mul_one, one_mul, inv_inv, mul_comm, mul_assoc])),
      ← `(tactic| simp only [mul_div, Nat.cast_mul]),
    ]

    -- Try multiplication-inverse equality pattern using sequence
    let mulInvEqInvTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [← div_eq_mul_inv, inv_eq_one_div]),
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence mulInvEqInvTactics then return

    -- Try simpler ofReal pattern
    if ← tryTactic (← `(tactic| simp only [ENNReal.ofReal_div_of_pos] <;> norm_num)) then return

    for tac in tactics do
      if ← tryTactic tac then return

    -- Try division equality pattern using sequence
    let divEqDivTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence divEqDivTactics then return

    -- Try basic division by self pattern
    if ← tryTactic (← `(tactic| simp only [ENNReal.div_self] <;> norm_num)) then return

    -- Try multiplication division cancellation pattern using sequence
    let mulDivCancelTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)])
    ]
    if ← tryTacticSequence mulDivCancelTactics then return

    -- Try simple inverse-multiplication to division pattern
    if ← tryTacticSequence [← `(tactic| rw [mul_comm, ← div_eq_mul_inv]), ← `(tactic| simp [ne_eq])] then return

    evalTactic (← `(tactic| all_goals assumption))

-- =============================================
-- FRACTION ADDITION TACTIC
-- =============================================

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
  -- First try basic simplification with zero addition
  -- if ← tryTactic (← `(tactic| simp only [add_zero, zero_add])) then return

  -- Try norm_num for simple arithmetic
  if ← tryTactic (← `(tactic| norm_num)) then return

  -- Convert inverses to divisions and simplify nested additions
  let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))

  -- Repeatedly combine additions with division
  repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

  -- Try inverse transformations
  let _ ← tryTactic (← `(tactic| ennreal_inv_transform))


  -- Try division by self for cases like 18/18 = 1
  if ← tryTactic (← `(tactic| ennreal_div_self)) then return

  -- If still not solved, try the toReal approach
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num),
    ]

  -- Final attempt with more aggressive rewriting
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| simp only [inv_eq_one_div]),
      ← `(tactic| rw [← ENNReal.add_div]),
      ← `(tactic| norm_num),
    ]


-- =============================================
-- TEST SUITES
-- =============================================

section MulDivAssocTests


-- Multiplication-division associativity lemmas
lemma test_mul_div_associativity_right {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_left {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

-- Concrete associativity examples
lemma test_mul_div_associativity_concrete : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

-- Cast preservation
lemma test_mul_div_associativity_preserves_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Division-multiplication associativity
lemma test_div_mul_associativity {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

end MulDivAssocTests

section InvPatternTests

-- Core inverse-division transformations
lemma test_inverse_multiplication_to_division {a b : ℕ} (ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform

lemma test_division_as_inverse_multiplication {a b : ℕ} :
  (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform

-- Double inverse property
lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by ennreal_inv_transform

-- Reciprocal patterns
lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by ennreal_inv_transform

-- Complex pattern example
lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_inv_transform

end InvPatternTests

section FractionAddTests

lemma test_nested_addition_division :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_fraction_add



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

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by
  ennreal_fraction_add



end FractionAddTests

end ENNRealArith
