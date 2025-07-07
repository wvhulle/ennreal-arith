import ENNRealArith.Common

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for proving ENNReal multiplication-division associativity.
Handles goals of the form `(↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal)`.
-/
syntax "ennreal_mul_div_assoc" : tactic

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


section TestSuite

-- Multiplication-division associativity lemmas
lemma test_mul_div_associativity_right {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_left {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

-- Concrete associativity examples
lemma test_mul_div_associativity_concrete_2_3_5 : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_concrete_4_1_7 : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_mul_div_assoc

-- Cast preservation
lemma test_mul_div_associativity_preserves_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Chain operations
lemma test_mul_div_associativity_chain {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  ennreal_mul_div_assoc

-- Special cases
lemma test_mul_div_associativity_denominator_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_multiplier_one {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Reciprocal identity
lemma test_reciprocal_multiplication_identity {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  ennreal_mul_div_assoc

-- Division-multiplication associativity
lemma test_div_mul_associativity {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_div_mul_associativity_concrete_6_2_3 : ((↑6 : ENNReal) / (↑2 : ENNReal)) * (↑3 : ENNReal) = (↑6 * ↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_mul_div_assoc

end TestSuite

end ENNRealArith
