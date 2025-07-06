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


lemma test_basic_add : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_basic_add_mul : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_basic_zero_one {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith


lemma test_div_self_basic {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

-- Note: This is testing the specific pattern ↑(n + 1) / ↑(n + 1) = 1
lemma test_div_self_succ (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_arith


lemma test_mul_cancel {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith


lemma test_mul_div_assoc {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_arith


lemma test_inv_mul {a b : ℕ} :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_arith


lemma test_complex : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

lemma test_generic_add {a b : ℕ} : (↑a : ENNReal) + ↑b = ↑(a + b) := by ennreal_arith
lemma test_generic_mul {a b : ℕ} : (↑a : ENNReal) * ↑b = ↑(a * b) := by ennreal_arith
lemma test_generic_div_self {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith
lemma test_generic_mul_div {a b c : ℕ} : (↑a : ENNReal) * (↑b / ↑c) = (↑a * ↑b) / ↑c := by ennreal_arith
lemma test_generic_inv_inv {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = ↑a := by ennreal_arith
lemma test_generic_zero_patterns : (0 : ENNReal) + 5 * 0 + 0 / 3 = 0 := by ennreal_arith
lemma test_generic_one_patterns {a : ℕ} : (↑a : ENNReal) * 1 / 1 * 1 = ↑a := by ennreal_arith

end Tests

end ENNRealArith

#lint
