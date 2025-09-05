import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

section DivisionTests

lemma test_eq_as_reals_inverse_1 : (5 : ENNReal)⁻¹ = 1 / (↑ 5) := by eq_as_reals

lemma test_fraction_div_one : (7 : ENNReal) / 1 = 7 := by eq_as_reals

lemma test_fraction_div_self_1 : (5 : ENNReal) / 5 = 1 := by eq_as_reals

lemma test_fraction_div_self_2 : (17 : ENNReal) / 17 = 1 := by eq_as_reals

lemma test_fraction_div_self_3 : (100 : ENNReal) / 100 = 1 := by eq_as_reals

lemma test_fraction_div_one_2 : (15 : ENNReal) / 1 = 15 := by eq_as_reals

lemma test_fraction_div_one_3 : (42 : ENNReal) / 1 = 42 := by eq_as_reals


lemma test_fraction_chain_1_auto : (12 : ENNReal) / 3 / 2 = 2 := by
  eq_as_reals

lemma test_large_fraction_3 : (5000 : ENNReal) / 1000 * 3 = 15 := by
  eq_as_reals

lemma test_fraction_chain_1_real : (12 : ENNReal) / 3 / 2 = 2 := by eq_as_reals

lemma test_eq_as_reals_1 : (100 : ENNReal) / 10 = 10 := by eq_as_reals

lemma test_eq_as_reals_2 : (200 : ENNReal) / 50 * 2 = 8 := by eq_as_reals

lemma test_eq_as_reals_3 : (1500 : ENNReal) / 300 / 5 = 1 := by eq_as_reals

lemma test_many_ops_3 : (6 : ENNReal) / 6 + 7 / 7 + 8 / 8 + 9 / 9 + 10 / 10 = 5 := by
  eq_as_reals

lemma test_div_stress_1 : (100 : ENNReal) / 1 / 1 / 1 / 1 / 1 = 100 := by eq_as_reals

lemma test_div_stress_2 : (50 : ENNReal) / 1 / 1 + 50 / 1 / 1 = 100 := by eq_as_reals

lemma test_div_stress_3 : (25 : ENNReal) / 1 * 4 / 1 = 100 := by eq_as_reals

lemma test_multi_div_1 : ((20 : ENNReal) / 4) / 1 = 5 := by eq_as_reals

lemma test_multi_div_2 : (30 : ENNReal) / (6 / 1) = 5 := by eq_as_reals

lemma test_multi_div_3 : ((40 : ENNReal) / 8) + ((50 / 10)) = 10 := by eq_as_reals

lemma test_large_fraction_1 : (1000 : ENNReal) / 100 = 10 := by eq_as_reals

lemma test_large_fraction_2 : (2000 : ENNReal) / 200 + 5 = 15 := by
  eq_as_reals

end DivisionTests

section InverseTests

lemma test_inverse_basic_1 : (5 : ENNReal)⁻¹ = 1 / 5 := by eq_as_reals

lemma test_inverse_basic_2 : (10 : ENNReal)⁻¹ = 1 / 10 := by eq_as_reals

lemma test_inverse_basic_3 : (2 : ENNReal)⁻¹ = 1 / 2 := by eq_as_reals

lemma test_inverse_stress_2 : (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = 3 * (4 : ENNReal)⁻¹ := by eq_as_reals

end InverseTests

section SupremumInfimumTests

lemma test_basic_supremum : (3 : ENNReal) ⊔ 5 = 5 := by eq_as_reals

lemma test_basic_infimum : (3 : ENNReal) ⊓ 5 = 3 := by eq_as_reals

lemma test_supremum_arithmetic : (2 : ENNReal) * (3 ⊔ 4) = 8 := by eq_as_reals

end SupremumInfimumTests
