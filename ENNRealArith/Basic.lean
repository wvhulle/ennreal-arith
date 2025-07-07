import ENNRealArith.BasicSimp
import ENNRealArith.DivSelf
import ENNRealArith.MulCancel
import ENNRealArith.MulDivAssoc
import ENNRealArith.InvPatterns
import ENNRealArith.FractionAdd


import ENNRealArith.Simp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Main ENNReal arithmetic tactic that combines multiple specialized tactics.
Tries basic simplification, division by self, multiplication cancellation,
multiplication/division associativity, inverse patterns, and fraction addition.
-/
syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let tactics : TSyntax `tactic := ← `(tactic| first
    | ennreal_basic_simp
    | ennreal_div_self
    | ennreal_mul_cancel
    | ennreal_mul_div_assoc
    | ennreal_inv_patterns
    | ennreal_fraction_add
    | fail "ennreal_arith could not solve the goal")

  evalTactic tactics

section Tests


lemma test_main_tactic_addition : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_addition_multiplication_precedence : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_multiplicative_additive_identity {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith




lemma test_multiplication_cancellation_right {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith


lemma test_mul_div_associativity {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_arith


lemma test_inverse_multiplication_to_division {a b : ℕ} :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_arith


lemma test_mixed_arithmetic_operations : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

lemma test_zero_absorbing_properties : (0 : ENNReal) + 5 * 0 + 0 / 3 = 0 := by ennreal_arith
lemma test_one_identity_chain {a : ℕ} : (↑a : ENNReal) * 1 / 1 * 1 = ↑a := by ennreal_arith




end Tests

end ENNRealArith

#lint
