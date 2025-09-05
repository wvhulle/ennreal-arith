import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

section BasicFailureTests

example: (1 : ENNReal) = 2 := by
  fail_if_success eq_as_reals
  sorry

example: (1 : ENNReal) > 2 := by
  fail_if_success eq_as_reals
  sorry

example: (2 : ENNReal) > 1 := by
  eq_as_reals

end BasicFailureTests

section SubtractionTests

example : (5 : ENNReal) - 2 = 5 := by
  fail_if_success eq_as_reals
  sorry

lemma test_subtraction_with_zero : (7 : ENNReal) - 0 = 7 := by
  simp

example : (10 : ENNReal) * 2 - 5 = 16 := by
  fail_if_success eq_as_reals
  sorry

end SubtractionTests

section EdgeCaseTests

lemma test_single_1 : (42 : ENNReal) = 42 := by eq_as_reals

lemma test_single_2 : (0 : ENNReal) = 0 := by eq_as_reals

lemma test_single_3 : (1 : ENNReal) = 1 := by eq_as_reals

lemma test_identity_1 : (7 : ENNReal) + 0 = 7 := by eq_as_reals

lemma test_identity_2 : (9 : ENNReal) * 1 = 9 := by eq_as_reals

lemma test_identity_3 : (15 : ENNReal) / 1 = 15 := by eq_as_reals

lemma test_zero_1 : (0 : ENNReal) + 15 = 15 := by eq_as_reals

lemma test_zero_2 : (0 : ENNReal) * 99 = 0 := by eq_as_reals

lemma test_zero_3 : (25 : ENNReal) * 0 = 0 := by eq_as_reals

lemma test_multiple_zeros_1 : (0 : ENNReal) + 0 + 0 = 0 := by eq_as_reals

lemma test_multiple_zeros_2 : (0 : ENNReal) * 0 * 0 = 0 := by eq_as_reals

lemma test_multiple_zeros_3 : (0 : ENNReal) + 0 + 0 + 0 + 0 = 0 := by eq_as_reals

lemma test_multiple_ones_1 : (1 : ENNReal) * 1 * 1 = 1 := by eq_as_reals

lemma test_multiple_ones_2 : (1 : ENNReal) + 1 + 1 = 3 := by eq_as_reals

lemma test_multiple_ones_3 : (1 : ENNReal) * 1 * 1 * 1 * 1 = 1 := by eq_as_reals

end EdgeCaseTests

section ExtendedRecognitionTests

lemma test_complex_mixed_operations : ((3 : ENNReal) + 2) * (4 ⊔ 6) - 1 = 35 := by
  fail_if_success eq_as_reals
  sorry

end ExtendedRecognitionTests

section ZeroOnePatterns

lemma test_zero_pattern_1 : (0 : ENNReal) + 0 + 0 + 5 = 5 := by eq_as_reals

lemma test_zero_pattern_2 : (10 : ENNReal) * 0 + 7 = 7 := by eq_as_reals

lemma test_zero_pattern_3 : (0 : ENNReal) * 100 + 8 * 1 = 8 := by eq_as_reals

lemma test_one_pattern_1 : (15 : ENNReal) * 1 * 1 = 15 := by eq_as_reals

lemma test_one_pattern_2 : (7 : ENNReal) * 1 + 3 * 1 = 10 := by eq_as_reals

end ZeroOnePatterns
