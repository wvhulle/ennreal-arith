import ENNRealArith.BasicSimp
import ENNRealArith.DivSelf
import ENNRealArith.MulCancel
import ENNRealArith.MulDivAssoc
import ENNRealArith.InvPatterns
import ENNRealArith.FractionAdd

-- Import the simp lemmas file which auto-registers with simp
import ENNRealArith.Simp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let tactics : Array (TSyntax `tactic) := #[
    ← `(tactic| ennreal_basic_simp),
    ← `(tactic| ennreal_fraction_add),
    ← `(tactic| ennreal_div_self),
    ← `(tactic| ennreal_mul_cancel),
    ← `(tactic| ennreal_mul_div_assoc),
    ← `(tactic| ennreal_inv_patterns)
  ]

  for tac in tactics do
    try
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => continue

  throwError "ennreal_arith could not solve the goal"

section Tests

-- Basic arithmetic tests
lemma test_basic_add : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_basic_add_mul : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_basic_zero_one {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

-- Division by self tests
lemma test_div_self_basic {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

-- Note: This is testing the specific pattern ↑(n + 1) / ↑(n + 1) = 1
lemma test_div_self_succ (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_arith

-- Multiplication cancellation tests
lemma test_mul_cancel {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith

-- Multiplication/division associativity tests
lemma test_mul_div_assoc {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_arith

-- Inverse pattern tests
lemma test_inv_mul {a b : ℕ} :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_arith

-- Complex expression test
lemma test_complex : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith


end Tests

end ENNRealArith
