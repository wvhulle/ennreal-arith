import ENNRealArith.Common

namespace ENNRealArith

/--
Tactic for basic ENNReal simplifications using norm_num, norm_cast, and simp.
Tries various combinations of these tactics to solve simple arithmetic goals.
-/
syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  if ← tryBasicComputation then return

  if ← tryTactic (← `(tactic| simp)) then return

  let tacticSequences := [
    [← `(tactic| norm_cast), ← `(tactic| norm_num)],
    [← `(tactic| simp only [add_zero, zero_add, inv_eq_one_div])],
    [← `(tactic| simp only [add_zero, zero_add]), ← `(tactic| norm_num)],
    [← `(tactic| rw [ENNReal.div_eq_div_iff]), ← `(tactic| all_goals norm_num)]
  ]

  for sequence in tacticSequences do
    if ← tryTacticSequence sequence then return

  throwError "ennreal_basic_simp could not solve the goal"

section TestSuite

-- Essential identity tests
lemma test_addition_right_identity {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by ennreal_basic_simp
lemma test_multiplication_right_identity {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by ennreal_basic_simp
lemma test_division_by_one_identity {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by ennreal_basic_simp

-- Key absorption properties
lemma test_multiplication_zero_absorbing {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by ennreal_basic_simp
lemma test_zero_divided_by_any {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by ennreal_basic_simp

-- Core concrete examples
lemma test_addition_concrete : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_basic_simp
lemma test_multiplication_concrete : (↑2 : ENNReal) * ↑3 = ↑6 := by ennreal_basic_simp

-- Cast preservation (essential for interoperability)
lemma test_addition_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by ennreal_basic_simp
lemma test_multiplication_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by ennreal_basic_simp

end TestSuite

end ENNRealArith

#lint
