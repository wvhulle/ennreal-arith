import ENNRealArith.ArithmeticCore
import ENNRealArith.FractionOperations

open Lean Meta Elab Tactic ENNReal

namespace ENNRealArith

/--
Main ENNReal arithmetic tactic that combines multiple specialized tactics.

This is the primary entry point for ENNReal arithmetic automation. It attempts
to solve goals involving ENNReal expressions by trying a sequence of specialized
tactics in order:

1. `ennreal_basic_simp` - Basic arithmetic simplification
2. `ennreal_div_self` - Division by self patterns
3. `ennreal_mul_cancel` - Multiplication cancellation in fractions
4. `ennreal_mul_div_assoc` - Multiplication/division associativity
5. `ennreal_inv_transform` - Inverse pattern transformations
6. `ennreal_fraction_add` - Fraction addition and simplification

The tactic will try each approach in sequence until one succeeds, or fail
with a descriptive error message if none apply.
-/
syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let tactics : TSyntax `tactic := ← `(tactic| first
    | ennreal_basic_simp
    | ennreal_div_self
    | ennreal_mul_cancel
    | ennreal_mul_div_assoc
    | ennreal_inv_transform
    | ennreal_fraction_add

    | fail "ennreal_arith could not solve the goal")

  evalTactic tactics

section Tests


lemma test_main_tactic_addition : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_addition_multiplication_precedence : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_multiplicative_additive_identity {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

example: (18 : ENNReal) / 18 = 1 := by ennreal_arith

example: @Eq ENNReal (18 / 18) 1 := by
  ennreal_arith

-- Test the exact pattern from user's error
example : @HDiv.hDiv ENNReal ENNReal ENNReal instHDiv 18 18 = @OfNat.ofNat ENNReal 1 One.toOfNat1 := by ennreal_arith

lemma test_division_self_nonzero_global {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_arith

lemma test_multiplication_cancellation_right {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith


lemma test_mul_div_associativity {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_arith

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by
  ennreal_fraction_add


lemma test_mixed_arithmetic_operations : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

lemma test_zero_absorbing_properties : (0 : ENNReal) + 5 * 0 + 0 / 3 = 0 := by ennreal_arith
lemma test_one_identity_chain {a : ℕ} : (↑a : ENNReal) * 1 / 1 * 1 = ↑a := by ennreal_arith

lemma test_simple_arithmetic: (2 : ENNReal) + 3 = 5 := by ennreal_arith


end Tests

end ENNRealArith

#lint
