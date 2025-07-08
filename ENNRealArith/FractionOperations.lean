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
Smart tactic for proving ENNReal multiplication-division associativity.
Handles goals of the form `(↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal)`
and other multiplication-division patterns.
-/
elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    -- Analyze goal patterns using our helper functions
    let patterns? ← analyzeEqualityGoal target

    match patterns? with
    | some (lhs, rhs) =>
      -- Use pattern-specific strategies with readable pattern matching
      let hasMultInDiv := lhs.hasMultiplicationInDivision || rhs.hasMultiplicationInDivision
      let hasSimpleArith := lhs.isSimpleArithmetic || rhs.isSimpleArithmetic

      if hasMultInDiv then
        -- For multiplication-division patterns, use mul_div laws
        if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return
      else if hasSimpleArith then
        -- For simple patterns, try basic arithmetic first
        if ← tryTactic (← `(tactic| norm_num)) then return
        if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, Nat.cast_mul])) then return

      -- Try the comprehensive approach
      if ← tryTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div, one_mul, mul_one, Nat.cast_mul])) then return

      -- Handle division by self cases with better error handling
      if ← tryTacticSequence [
        ← `(tactic| apply ENNReal.div_self),
        ← `(tactic| apply Nat.cast_ne_zero.mpr),
        ← `(tactic| assumption),
        ← `(tactic| exact ENNReal.coe_ne_top)
      ] then return

    | none =>
      -- Not an equality goal
      throwError "ennreal_mul_div_assoc expects an equality goal"

    throwError "ennreal_mul_div_assoc could not solve the goal"

-- =============================================
-- INVERSE PATTERN TRANSFORMATION TACTIC
-- =============================================

syntax "ennreal_inv_transform" : tactic

/--
Smart tactic for transforming ENNReal inverse and division expressions.
Analyzes goal structure to efficiently handle transformations involving inverses,
divisions, and multiplications. Converts between forms like `a⁻¹ * b = b / a` and `(a⁻¹)⁻¹ = a`.
-/
elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget

    -- Try basic reflexivity first
    if ← tryTactic (← `(tactic| rfl)) then return

    -- Analyze goal patterns using our helper functions
    let patterns? ← analyzeEqualityGoal target

    match patterns? with
    | some (lhs, rhs) =>
      -- Use pattern-specific strategies with readable pattern matching
      let hasDoubleInv := lhs.hasDoubleInverse || rhs.hasDoubleInverse
      let hasInverse := lhs.hasInverse || rhs.hasInverse
      let hasDivision := lhs.hasDivision || rhs.hasDivision
      let hasInvMulDiv := lhs.hasMultiplicationInDivision || rhs.hasMultiplicationInDivision

      if hasDoubleInv then
        -- Handle double inverse patterns first, including (1/a)⁻¹ = a
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, one_div])) then return

      if hasInverse && hasDivision then
        -- Handle inverse-multiplication to division conversion
        if ← tryTactic (← `(tactic| simp only [div_eq_mul_inv, mul_comm])) then return

      if hasInverse && !hasDivision then
        -- Pure inverse transformations
        if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div, mul_one, one_mul])) then return

      if hasInvMulDiv then
        -- Complex patterns that might need mul_div_assoc
        if ← tryTacticSequence [
          ← `(tactic| simp only [one_div, inv_inv]),
          ← `(tactic| ennreal_mul_div_assoc)
        ] then return

      -- Try comprehensive simp if specific patterns didn't work
      if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                             div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul])) then return

    | none =>
      -- Not an equality goal, try basic approach
      if ← tryTactic (← `(tactic| simp only [inv_inv, inv_eq_one_div])) then return

    -- Fallback tactics for remaining cases
    let remainingTactics := [
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| simp only [mul_div, Nat.cast_mul])
    ]

    for tac in remainingTactics do
      if ← tryTactic tac then return

    -- Try division equality patterns
    if ← tryTacticSequence [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ] then return

    -- Final fallback
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

/--
Smart tactic for simplifying ENNReal expressions with additions and fractions.
Uses pattern analysis to efficiently handle different types of fraction operations.
-/
elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget
    
    -- Try norm_num first for simple arithmetic
    if ← tryTactic (← `(tactic| norm_num)) then return

    -- Analyze goal patterns using our helper functions
    let patterns? ← analyzeEqualityGoal target
    
    -- Check for concrete division patterns first for early exit
    if isConcreteDivisionGoal target then
      if ← tryTactic (← `(tactic| ennreal_div_self)) then return
    
    -- Use pattern analysis to optimize approach
    match patterns? with
    | some (lhs, rhs) =>
      let hasInverse := lhs.hasInverse || rhs.hasInverse
      let hasAddition := lhs.hasAddition || rhs.hasAddition
      let isSimpleArithmetic := lhs.isSimpleArithmetic && rhs.isSimpleArithmetic
      
      if isSimpleArithmetic then
        -- For simple arithmetic, try basic identities first
        if ← tryTactic (← `(tactic| simp only [add_zero, zero_add, mul_one, one_mul])) then return
      
      if hasInverse then
        -- For inverse patterns, convert to divisions first
        let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))
        let _ ← tryTactic (← `(tactic| ennreal_inv_transform))
        -- For complex inverse addition, try norm_num1 to simplify OfNat patterns
        if hasAddition then
          let _ ← tryTactic (← `(tactic| norm_num1))
      else if hasAddition then
        -- For addition patterns, focus on combining terms
        let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add]))
      
    | none =>
      -- Not an equality goal, use basic approach
      let _ ← tryTactic (← `(tactic| simp only [add_zero, zero_add]))
    
    -- Common steps for all patterns
    -- Convert inverses to divisions and simplify nested additions  
    let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))

    -- Repeatedly combine additions with division
    repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

    -- Try inverse transformations
    let _ ← tryTactic (← `(tactic| ennreal_inv_transform))

    -- Try division by self for cases like 18/18 = 1
    if ← tryTactic (← `(tactic| ennreal_div_self)) then return

    -- Check if goal is solved after pattern-specific attempts
    if (← getUnsolvedGoals).isEmpty then return

    -- If still not solved, try the toReal approach
    if ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num)
    ] then return

    -- Final attempt with more aggressive rewriting
    if ← tryTacticSequence [
      ← `(tactic| simp only [inv_eq_one_div]),
      ← `(tactic| rw [← ENNReal.add_div]),
      ← `(tactic| norm_num)
    ] then return
    
    -- If all attempts failed, provide informative error
    throwError "ennreal_fraction_add could not solve the goal"


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
lemma test_inverse_multiplication_to_division {a b : ℕ} (_ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform

lemma test_division_as_inverse_multiplication {a b : ℕ} :
  (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform

-- Double inverse property
lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  simp only [inv_inv]

-- Reciprocal patterns
lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  simp only [inv_eq_one_div]

-- Complex pattern example
lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp only [one_div, inv_inv, mul_div]

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
