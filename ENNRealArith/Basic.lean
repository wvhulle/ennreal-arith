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

lemma test123: ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_arith

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

-- Test case from user's density_sum_one proof that currently fails
-- This test demonstrates the issue where ennreal_arith can't prove 18/18 = 1
-- after simplifying a complex nested addition
lemma test_nested_addition_division_fails :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
 ennreal_arith -- sorry -- ennreal_arith fails here!

-- The core issue: ennreal_arith fails on concrete division after simplification
lemma test_concrete_division_18_fails : (18 : ENNReal) / 18 = 1 := by
  ennreal_arith -- fails here!

-- But ennreal_fraction_add succeeds on the same goal
lemma test_nested_addition_division_fraction_add_succeeds :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_fraction_add

-- Manual proof showing what should work
lemma test_concrete_division_18_manual : (18 : ENNReal) / 18 = 1 := by
  apply ENNReal.div_self <;> norm_num

-- This simulates what happens in the user's proof after split_ifs
-- The first ennreal_arith simplifies the nested sum but then fails on 18/18 = 1
lemma test_simulating_user_issue :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  -- First attempt: ennreal_arith partially succeeds by using norm_num to simplify to 18/18 = 1
  -- but then fails to prove that final step
  ennreal_arith
  -- sorry -- Replace with: ennreal_arith (this would fail with "18 / 18 = 1" remaining)

-- Test showing the workaround pattern from the user
lemma test_user_workaround :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  -- This mimics the user's solution of calling ennreal_arith multiple times
  first | ennreal_arith


-- Test simulating split_ifs with multiple goals
lemma test_split_ifs_simulation (p q : Prop) [Decidable p] [Decidable q] :
  (if p then (0 : ENNReal) else if q then 1/18 else
    ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18) =
  (if p then 0 else if q then 1/18 else 1) := by
  split_ifs <;> ennreal_arith


end Tests

end ENNRealArith
