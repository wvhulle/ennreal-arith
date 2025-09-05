import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

section StressTests

lemma test_stress_fibonacci_pattern :
  let a := (1 : ENNReal)
  let b := (1 : ENNReal)
  let c := a + b
  let d := b + c
  let e := c + d
  let f := d + e
  a + b + c + d + e + f = 20 := by eq_as_reals

lemma test_stress_factorial_pattern :
  (1 : ENNReal) * (1 + 1) * (1 + 1 + 1) * (1 + 1 + 1 + 1) * (1 + 1 + 1 + 1 + 1) = 120 := by eq_as_reals

end StressTests

section FractionStressTests

lemma test_max_stress_1 : ((((2 : ENNReal) / 1) + 3) / 1 + 4) / 1 = 9 := by eq_as_reals

lemma test_max_stress_2 : (((5 : ENNReal)⁻¹ + (5 : ENNReal)⁻¹) + 0) + 0 = 2 * (5 : ENNReal)⁻¹ := by eq_as_reals

lemma test_max_stress_3 : ((10 : ENNReal) / 10 + 20 / 20 + 30 / 30) * 2 = 6 := by
  eq_as_reals

end FractionStressTests

section FinalStressTests

lemma test_max_nesting_1 : ((((((1 : ENNReal) + 1) + 1) + 1) + 1) + 1) + 1 = 7 := by eq_as_reals

lemma test_max_nesting_2 : ((((((2 : ENNReal) * 2) + 1) + 1) + 1) + 1) + 1 = 9 := by eq_as_reals

lemma test_max_nesting_3 : (((((((3 : ENNReal) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 10 := by eq_as_reals

lemma test_very_long_1 : (1 : ENNReal) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 15 := by eq_as_reals

lemma test_very_long_2 : (2 : ENNReal) + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 26 := by eq_as_reals

lemma test_very_long_3 : (1 : ENNReal) * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 = 1 := by eq_as_reals

end FinalStressTests
