import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

section CoercionTests

lemma test_real_coercion : ENNReal.ofReal 3.5 + ENNReal.ofReal 1.5 = 5 := by eq_as_reals

lemma test_mixed_coercions : (↑(2 : ℕ) : ENNReal) + ENNReal.ofReal 3.0 = 5 := by eq_as_reals

lemma test_coercion_literal : (↑(3 : ℕ) : ENNReal) + (↑(4 :
  ℕ) : ENNReal) = 7 := by eq_as_reals

lemma test_nnreal_coercion : (↑(3 : NNReal) : ENNReal) + (↑(4
   : NNReal) : ENNReal) = 7 := by eq_as_reals

lemma test_decimal_nnreal : (↑(3.5 : NNReal) : ENNReal) + (↑(1.5 : NNReal) : ENNReal) = 5 := by eq_as_reals

end CoercionTests

section InfinityTests

lemma test_infinity_addition : (⊤ : ENNReal) + 1 = ⊤ := by
  rfl

lemma test_infinity_subtraction : (⊤ : ENNReal) - 5 = ⊤ := by eq_as_reals

end InfinityTests