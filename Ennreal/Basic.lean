/-
Main ENNReal arithmetic tactics module.
Combines all sub-tactics into comprehensive automation.
-/
import Ennreal.BasicSimp
import Ennreal.DivSelf
import Ennreal.MulCancel
import Ennreal.MulDivAssoc
import Ennreal.InvPatterns
-- import Ennreal.SimpAll

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

-- =============================================================================
-- MAIN COMBINED TACTIC
-- =============================================================================

-- Main tactic that tries all modular components in order
syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let goal ← getMainGoal
  goal.withContext do

    -- Try basic simplifications first
    try
      evalTactic (← `(tactic| ennreal_basic_simp))
      return
    catch _ => pure ()

    -- Try division self-cancellation patterns
    try
      evalTactic (← `(tactic| ennreal_div_self))
      return
    catch _ => pure ()

    -- Try multiplication cancellation patterns
    try
      evalTactic (← `(tactic| ennreal_mul_cancel))
      return
    catch _ => pure ()

    -- Try multiplication-division associativity
    try
      evalTactic (← `(tactic| ennreal_mul_div_assoc))
      return
    catch _ => pure ()

    -- Try inverse patterns
    try
      evalTactic (← `(tactic| ennreal_inv_patterns))
      return
    catch _ => pure ()

    -- All specific tactics tried, no fallback needed

    throwError "ennreal_arith could not solve the goal"

-- =============================================================================
-- CONVENIENCE COMBINATION TACTICS
-- =============================================================================

-- Try all division patterns (self-cancellation and multiplication cancellation)
syntax "ennreal_div_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_div_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| ennreal_div_self))
      return
    catch _ => pure ()

    try
      evalTactic (← `(tactic| ennreal_mul_cancel))
      return
    catch _ => pure ()

    throwError "ennreal_div_patterns could not solve the goal"

-- Try all rewrite-based patterns
syntax "ennreal_rewrite_patterns" : tactic

elab_rules : tactic | `(tactic| ennreal_rewrite_patterns) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| ennreal_mul_div_assoc))
      return
    catch _ => pure ()

    try
      evalTactic (← `(tactic| ennreal_inv_patterns))
      return
    catch _ => pure ()

    throwError "ennreal_rewrite_patterns could not solve the goal"

-- Try all simplification patterns
syntax "ennreal_simplify" : tactic

elab_rules : tactic | `(tactic| ennreal_simplify) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| ennreal_basic_simp))
      return
    catch _ => pure ()

    -- All basic tactics tried

    throwError "ennreal_simplify could not solve the goal"

-- =============================================================================
-- INTEGRATION TEST SUITE
-- =============================================================================

section IntegrationTests

-- Test that all individual tactics still work
lemma test_basic_simp : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_basic_simp

lemma test_div_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_div_self

lemma test_mul_cancel {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel

lemma test_mul_div_assoc {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_mul_div_assoc

lemma test_inv_patterns {a b c : ℕ} : (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_inv_patterns

lemma test_basic_complex {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_basic_simp

-- Test that the main tactic works for all patterns
lemma test_main_basic : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_main_div_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

lemma test_main_mul_cancel {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith

lemma test_main_mul_div_assoc {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_arith

lemma test_main_complex {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

-- Test convenience tactics
lemma test_div_patterns_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_div_patterns

lemma test_div_patterns_cancel {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_div_patterns

lemma test_rewrite_patterns_assoc {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_rewrite_patterns

lemma test_simplify_basic : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_simplify

lemma test_simplify_complex {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_simplify

end IntegrationTests

end ENNRealArith
