/-
Comprehensive simplification tactics for ENNReal arithmetic.
Handles complex cases that require multiple rewrites and simplifications.
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
-- COMPREHENSIVE SIMPLIFICATION TACTIC
-- =============================================================================

-- Comprehensive ENNReal simplification
syntax "ennreal_simp_all" : tactic

elab_rules : tactic | `(tactic| ennreal_simp_all) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| simp only [ENNReal.coe_zero, ENNReal.coe_one, ENNReal.coe_add, ENNReal.coe_mul,
                                         ENNReal.add_zero, ENNReal.zero_add, ENNReal.mul_one, ENNReal.one_mul,
                                         ENNReal.mul_zero, ENNReal.zero_mul, ENNReal.div_one, ENNReal.zero_div,
                                         ENNReal.pow_zero, ENNReal.pow_one, ENNReal.one_pow,
                                         mul_div, ENNReal.div_eq_inv_mul, one_mul, inv_inv]))
      return
    catch _ => pure ()

    throwError "ennreal_simp_all could not solve the goal"

-- =============================================================================
-- TEST SUITE: COMPREHENSIVE SIMPLIFICATION EXAMPLES
-- =============================================================================

section TestSuite

-- =============================================================================
-- TRIVIAL DIVISION CASES
-- =============================================================================

lemma ennreal_div_cast_manual {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  rfl

lemma ennreal_div_cast {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_simp_all

-- =============================================================================
-- BASIC DIVISION WITH FRACTIONS
-- =============================================================================

lemma ennreal_add_div_cast_manual {a b c : ℕ} : (↑a + ↑b : ENNReal) / ↑c = (↑(a + b) : ENNReal) / ↑c := by
  rw [← ENNReal.coe_add]

lemma ennreal_add_div_cast {a b c : ℕ} : (↑a + ↑b : ENNReal) / ↑c = (↑(a + b) : ENNReal) / ↑c := by
  ennreal_simp_all

lemma ennreal_toReal_div_nat_manual {a b : ℕ} : ((↑a : ENNReal) / ↑b).toReal = (a : ℝ) / (b : ℝ) := by
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal]

lemma ennreal_toReal_div_nat {a b : ℕ} : ((↑a : ENNReal) / ↑b).toReal = (a : ℝ) / (b : ℝ) := by
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal]

-- =============================================================================
-- COMPLEX EXPRESSIONS WITH MULTIPLE OPERATIONS
-- =============================================================================

lemma ennreal_complex_expr_manual {a b c d : ℕ} :
  (↑a : ENNReal) * 1 + 0 * ↑b + (↑c : ENNReal) ^ 1 / 1 = ↑a + ↑c := by
  simp only [ENNReal.mul_one, ENNReal.zero_mul, ENNReal.add_zero, ENNReal.zero_add,
             ENNReal.pow_one, ENNReal.div_one]

lemma ennreal_complex_expr {a b c d : ℕ} :
  (↑a : ENNReal) * 1 + 0 * ↑b + (↑c : ENNReal) ^ 1 / 1 = ↑a + ↑c := by
  ennreal_simp_all

lemma ennreal_nested_expr_manual {a b c : ℕ} :
  ((↑a : ENNReal) + 0) * (1 * (↑b : ENNReal)) / (1 * (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / ↑c := by
  simp only [ENNReal.add_zero, ENNReal.one_mul, ENNReal.mul_one]

lemma ennreal_nested_expr {a b c : ℕ} :
  ((↑a : ENNReal) + 0) * (1 * (↑b : ENNReal)) / (1 * (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / ↑c := by
  ennreal_simp_all

-- =============================================================================
-- POWER AND MULTIPLICATION COMBINATIONS
-- =============================================================================

lemma ennreal_power_mul_manual {a b : ℕ} :
  (↑a : ENNReal) ^ 1 * (↑b : ENNReal) ^ 0 = ↑a := by
  simp only [ENNReal.pow_one, ENNReal.pow_zero, ENNReal.mul_one]

lemma ennreal_power_mul {a b : ℕ} :
  (↑a : ENNReal) ^ 1 * (↑b : ENNReal) ^ 0 = ↑a := by
  ennreal_simp_all

lemma ennreal_one_power_manual {n : ℕ} :
  (1 : ENNReal) ^ n * (↑2 : ENNReal) ^ 0 / 1 = 1 := by
  simp only [ENNReal.one_pow, ENNReal.pow_zero, ENNReal.mul_one, ENNReal.div_one]

lemma ennreal_one_power {n : ℕ} :
  (1 : ENNReal) ^ n * (↑2 : ENNReal) ^ 0 / 1 = 1 := by
  ennreal_simp_all

-- =============================================================================
-- ZERO AND ONE INTERACTIONS
-- =============================================================================

lemma ennreal_zero_one_expr_manual {a : ℕ} :
  0 + (↑a : ENNReal) * 1 * 1 + 0 / ↑a = ↑a := by
  simp only [ENNReal.zero_add, ENNReal.mul_one, ENNReal.add_zero, ENNReal.zero_div]

lemma ennreal_zero_one_expr {a : ℕ} :
  0 + (↑a : ENNReal) * 1 * 1 + 0 / ↑a = ↑a := by
  ennreal_simp_all

lemma ennreal_mul_zero_expr_manual {a b : ℕ} :
  (↑a : ENNReal) * 0 + 0 * ↑b + ↑a * 1 = ↑a := by
  simp only [ENNReal.mul_zero, ENNReal.zero_mul, ENNReal.zero_add, ENNReal.add_zero, ENNReal.mul_one]

lemma ennreal_mul_zero_expr {a b : ℕ} :
  (↑a : ENNReal) * 0 + 0 * ↑b + ↑a * 1 = ↑a := by
  ennreal_simp_all

-- =============================================================================
-- DIVISION PATTERNS
-- =============================================================================

lemma ennreal_div_zero_expr_manual {a b : ℕ} :
  0 / (↑a : ENNReal) + (↑b : ENNReal) / 1 = ↑b := by
  simp only [ENNReal.zero_div, ENNReal.zero_add, ENNReal.div_one]

lemma ennreal_div_zero_expr {a b : ℕ} :
  0 / (↑a : ENNReal) + (↑b : ENNReal) / 1 = ↑b := by
  ennreal_simp_all

-- =============================================================================
-- INVERSE PATTERNS WITH SIMPLIFICATION
-- =============================================================================

lemma ennreal_inv_simp_manual {a b : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * 1 = ↑a := by
  simp only [ENNReal.div_eq_inv_mul, one_mul, inv_inv]

lemma ennreal_inv_simp {a b : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * 1 = ↑a := by
  ennreal_simp_all

-- =============================================================================
-- MULTIPLICATION AND DIVISION CHAINS
-- =============================================================================

lemma ennreal_mul_div_chain_simp_manual {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) * 1 = (↑a * ↑b : ENNReal) / ↑c := by
  simp only [mul_div, ENNReal.mul_one]

lemma ennreal_mul_div_chain_simp {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) * 1 = (↑a * ↑b : ENNReal) / ↑c := by
  ennreal_simp_all

end TestSuite

end ENNRealArith
