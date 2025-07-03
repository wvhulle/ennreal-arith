/-
Inverse pattern tactics for ENNReal arithmetic.
Handles patterns involving division and inverse relationships.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

-- =============================================================================
-- INVERSE PATTERNS TACTIC
-- =============================================================================

-- Inverse patterns (handling division and inverse relationships)
syntax "ennreal_inv_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    -- Helper function to try a pattern and return success
    let tryPattern (tac : TSyntax `tactic) : TacticM Bool := do
      try
        let goals_before ← getUnsolvedGoals
        if goals_before.isEmpty then return true
        evalTactic tac
        let goals_after ← getUnsolvedGoals
        return goals_after.isEmpty
      catch _ => return false

    -- Define all tactics to try in order from simple to complex
    let tactics : Array (TSyntax `tactic) := #[
      -- 1. Definitional equality
      ← `(tactic| rfl),

      -- 2. Simple inverse patterns
      ← `(tactic| rw [inv_inv]),

      -- 3. Division/multiplication conversions
      ← `(tactic| rw [ENNReal.div_eq_inv_mul]),
      ← `(tactic| rw [ENNReal.div_eq_inv_mul, mul_comm]),
      ← `(tactic| rw [← ENNReal.div_eq_inv_mul]),
      ← `(tactic| rw [← ENNReal.div_eq_inv_mul, mul_comm]),
      ← `(tactic| rw [div_eq_mul_inv]),
      ← `(tactic| rw [← div_eq_mul_inv]),

      -- 4. Inverse to division: a⁻¹ = 1 / a
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| rw [← inv_eq_one_div]),

      -- 5. Basic operations
      ← `(tactic| rw [mul_comm]),
      ← `(tactic| rw [mul_one]),
      ← `(tactic| rw [one_mul]),

      -- 6. Complex patterns (from working manual proofs)
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]),
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv]),
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv, mul_comm]),
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm]),
      ← `(tactic| simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm, mul_assoc]),

      -- 7. simp with mul_div for complex patterns
      ← `(tactic| simp),
      ← `(tactic| simp [mul_div]),
      ← `(tactic| simp only [mul_div]),
      ← `(tactic| rw [mul_div]),

      -- 8. More patterns for commutativity/associativity
      ← `(tactic| simp only [mul_comm, mul_assoc])
    ]

    -- Try each tactic until one succeeds
    for tac in tactics do
      if ← tryPattern tac then return

    throwError "ennreal_inv_patterns could not solve the goal"

-- =============================================================================
-- TEST SUITE: INVERSE PATTERNS EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- LEVEL 1: TRIVIAL CASES - DEFINITIONAL EQUALITY
-- =============================================================================

-- These should work with `rfl` because they are definitionally equal
lemma ennreal_three_div_two_concrete_manual : (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ = (↑3 : ENNReal) / (↑2 : ENNReal) := by
  rfl  -- This works! They are definitionally equal

lemma ennreal_three_div_two_concrete : (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ = (↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 2: SIMPLE SINGLE REWRITES
-- =============================================================================

-- Double inverse: (a⁻¹)⁻¹ = a
lemma ennreal_inv_inv_manual {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  rw [inv_inv]

lemma ennreal_inv_inv {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

-- Division to multiplication: a / b = a * b⁻¹
lemma ennreal_div_eq_inv_mul_manual {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, mul_comm]

lemma ennreal_div_eq_inv_mul {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by
  ennreal_inv_patterns

-- Multiplication to division: a * b⁻¹ = a / b
lemma ennreal_mul_inv_manual {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  rfl  -- This is definitionally equal

lemma ennreal_mul_inv {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal)⁻¹ = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 3: SIMPLE COMMUTATIVITY
-- =============================================================================

-- Multiplication commutativity with inverses: a⁻¹ * b = b * a⁻¹
lemma ennreal_inv_two_mul_three_manual : (↑2 : ENNReal)⁻¹ * (↑3 : ENNReal) = (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ := by
  rw [mul_comm]

lemma ennreal_inv_two_mul_three : (↑2 : ENNReal)⁻¹ * (↑3 : ENNReal) = (↑3 : ENNReal) * (↑2 : ENNReal)⁻¹ := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 4: ONE WITH DIVISION AND INVERSES
-- =============================================================================

-- 1 / a = a⁻¹
lemma ennreal_one_div_eq_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, mul_one]

lemma ennreal_one_div_eq_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by
  ennreal_inv_patterns

-- 1 / a⁻¹ = a
lemma ennreal_one_div_inv_manual {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  rw [ENNReal.div_eq_inv_mul, mul_one, inv_inv]

lemma ennreal_one_div_inv {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal)⁻¹ = (↑a : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 5: CONCRETE INVERSE EXAMPLES
-- =============================================================================

-- Concrete examples with specific numbers
lemma ennreal_two_inv_manual : (↑2 : ENNReal)⁻¹ = 1 / (↑2 : ENNReal) := by
  rw [inv_eq_one_div]

lemma ennreal_two_inv : (↑2 : ENNReal)⁻¹ = 1 / (↑2 : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_three_inv_manual : (↑3 : ENNReal)⁻¹ = 1 / (↑3 : ENNReal) := by
  rw [inv_eq_one_div]

lemma ennreal_three_inv : (↑3 : ENNReal)⁻¹ = 1 / (↑3 : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 6: CONCRETE COMPLEX EXAMPLES
-- =============================================================================

-- (1 / a)⁻¹ * (b / c) = (a * b) / c - concrete version
lemma ennreal_one_div_two_inv_mul_three_div_seven_manual :
  (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑7 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑7 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]
  simp only [mul_comm, mul_assoc]

lemma ennreal_one_div_two_inv_mul_three_div_seven :
  (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑7 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_inv_patterns

lemma ennreal_two_inv_three_manual : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv, mul_comm, mul_assoc]

lemma ennreal_two_inv_three : (1 / (↑2 : ENNReal))⁻¹ * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 7: GENERIC COMPLEX WITH CASTING
-- =============================================================================

lemma ennreal_inv_div_mul_div_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  simp
  rw [mul_div]

lemma ennreal_inv_div_mul_div {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

-- =============================================================================
-- LEVEL 8: MOST COMPLEX WITH REARRANGEMENT
-- =============================================================================

-- (1 / a)⁻¹ * (b / c) = (a * b) / c - requires complex rearrangement
lemma ennreal_complex_inv_manual {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  simp
  rw [mul_div]

lemma ennreal_complex_inv {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_inv_patterns

end TestSuite

end ENNRealArith
