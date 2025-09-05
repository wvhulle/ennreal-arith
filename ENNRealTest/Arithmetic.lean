import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

section BasicArithmeticTests

lemma test_with_vars {a b : ENNReal} :
  a + b = b + a := by
  eq_as_reals

example: 0 ≤ (ENNReal.ofReal 0).toReal + ((ENNReal.ofReal 0).toReal + (ENNReal.ofReal 0).toReal) := by
  eq_as_reals

lemma test_advanced_basic : (2 : ENNReal) + 3 = 5 := by eq_as_reals

lemma test_advanced_multiplication : (2 : ENNReal) * 3 * 4 = 24 := by eq_as_reals

lemma test_advanced_zero_handling : (5 : ENNReal) + 0 * 100 = 5 := by eq_as_reals

lemma test_basic_addition_check : (2 : ENNReal) + 3 = 5 := by eq_as_reals

lemma test_basic_multiplication_check : (2 : ENNReal) * 3 = 6 := by eq_as_reals

end BasicArithmeticTests

section ComplexNestedTests

lemma test_deeply_nested_addition_1 :
  ((((1 : ENNReal) + 2) + 3) + ((4 + 5) + 6)) = 21 := by eq_as_reals

lemma test_deeply_nested_addition_2 :
  (((1 : ENNReal) + (2 + 3)) + ((4 + 5) + (6 + 7))) = 28 := by eq_as_reals

lemma test_deeply_nested_multiplication_simpler :
  ((2 : ENNReal) * 3) * ((4 * 5) * 6) = 720 := by eq_as_reals

lemma test_mixed_nested_operations_1 :
  ((2 : ENNReal) + 3) * ((4 + 1) * (6 + 0)) = 150 := by eq_as_reals

lemma test_mixed_nested_operations_2 :
  (((1 : ENNReal) + 2) + 3) * (((4 + 5) + 6) + 7) = 132 := by eq_as_reals

lemma test_moderately_deep_nesting :
  (((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) = 7 := by eq_as_reals

lemma test_extremely_deep_nesting :
  (((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) + (((1 + 1) + (1 + 1)) + ((1 + 1) + (1 + 1))) = 15 := by eq_as_reals

end ComplexNestedTests

section LargeNumberTests

lemma test_long_addition_chain :
  (1 : ENNReal) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by eq_as_reals

lemma test_long_multiplication_chain :
  (1 : ENNReal) * 2 * 3 * 4 * 5 = 120 := by eq_as_reals

lemma test_large_number_arithmetic :
  (100 : ENNReal) + 200 + 300 + 400 + 500 = 1500 := by eq_as_reals

lemma test_very_large_arithmetic :
  (1000 : ENNReal) + 2000 + 3000 = 6000 := by eq_as_reals

lemma test_large_addition_1 : (100 : ENNReal) + 200 + 300 = 600 := by eq_as_reals

lemma test_large_addition_2 : (1000 : ENNReal) + 2000 + 3000 + 4000 = 10000 := by eq_as_reals

lemma test_large_multiplication_1 : (100 : ENNReal) * 5 = 500 := by eq_as_reals

lemma test_large_multiplication_2 : (50 : ENNReal) * 20 = 1000 := by eq_as_reals

lemma test_large_1 : (1000 : ENNReal) + 2000 + 3000 + 4000 + 5000 = 15000 := by eq_as_reals

lemma test_large_2 : (10000 : ENNReal) + 20000 + 30000 = 60000 := by eq_as_reals

lemma test_large_3 : (50000 : ENNReal) + 50000 = 100000 := by eq_as_reals

lemma test_large_mul_1 : (1000 : ENNReal) * 10 = 10000 := by eq_as_reals

lemma test_large_mul_2 : (500 : ENNReal) * 20 = 10000 := by eq_as_reals

lemma test_large_mul_3 : (250 : ENNReal) * 40 = 10000 := by eq_as_reals

lemma test_large_mixed_1 : (1000 : ENNReal) + 2000 * 3 = 7000 := by eq_as_reals

lemma test_large_mixed_2 : (500 : ENNReal) * 2 + 3000 = 4000 := by eq_as_reals

lemma test_large_mixed_3 : (100 : ENNReal) * 10 + 200 * 5 = 2000 := by eq_as_reals

end LargeNumberTests

section DistributivityTests

lemma test_distributivity_complex_1 :
  ((2 : ENNReal) + 3) * (4 + 5) = 2 * 4 + 2 * 5 + 3 * 4 + 3 * 5 := by eq_as_reals

lemma test_distributivity_complex_2 :
  ((1 : ENNReal) + 2) * ((3 + 4) + (5 + 6)) = 3 * 18 := by eq_as_reals

lemma test_distributivity_with_zero :
  ((5 : ENNReal) + 0) * ((3 + 0) + (2 + 0)) = 25 := by eq_as_reals

lemma test_distributive_1 : (2 : ENNReal) * (3 + 4) = 2 * 3 + 2 * 4 := by eq_as_reals

lemma test_distributive_2 : (5 : ENNReal) * (6 + 7) = 5 * 6 + 5 * 7 := by eq_as_reals

lemma test_distributive_3 : (1 : ENNReal) * (10 + 20 + 30) = 1 * 10 + 1 * 20 + 1 * 30 := by eq_as_reals

lemma test_left_distributive_1 : ((3 : ENNReal) + 4) * 5 = 3 * 5 + 4 * 5 := by eq_as_reals

lemma test_left_distributive_2 : ((7 : ENNReal) + 8) * 9 = 7 * 9 + 8 * 9 := by eq_as_reals

lemma test_complex_distributive_1 : (2 : ENNReal) * (3 + 4) + 5 * (6 + 7) = 14 + 65 := by eq_as_reals

lemma test_complex_distributive_2 : (1 : ENNReal) * (2 + 3) * (4 + 5) = 5 * 9 := by eq_as_reals

lemma test_factoring_1 : (6 : ENNReal) + 9 = 3 * (2 + 3) := by eq_as_reals

lemma test_factoring_2 : (10 : ENNReal) + 15 = 5 * (2 + 3) := by eq_as_reals

lemma test_factoring_3 : (12 : ENNReal) + 18 + 24 = 6 * (2 + 3 + 4) := by eq_as_reals

end DistributivityTests

section AssociativityTests

lemma test_associativity_addition_complex :
  ((1 : ENNReal) + (2 + 3)) + (4 + 5) = (1 + 2) + ((3 + 4) + 5) := by eq_as_reals

lemma test_associativity_multiplication_complex :
  ((2 : ENNReal) * (3 * 4)) * (5 * 6) = (2 * 3) * ((4 * 5) * 6) := by eq_as_reals

lemma test_mixed_associativity :
  ((1 : ENNReal) + 2) * ((3 + 4) * 5) = 1 * 3 * 5 + 1 * 4 * 5 + 2 * 3 * 5 + 2 * 4 * 5 := by eq_as_reals

lemma test_add_assoc_1 : ((1 : ENNReal) + 2) + 3 = 1 + (2 + 3) := by eq_as_reals

lemma test_add_assoc_2 : ((5 : ENNReal) + 6) + 7 = 5 + (6 + 7) := by eq_as_reals

lemma test_add_assoc_3 : (((10 : ENNReal) + 11) + 12) + 13 = 10 + ((11 + 12) + 13) := by eq_as_reals

lemma test_mul_assoc_1 : ((2 : ENNReal) * 3) * 4 = 2 * (3 * 4) := by eq_as_reals

lemma test_mul_assoc_2 : ((5 : ENNReal) * 6) * 7 = 5 * (6 * 7) := by eq_as_reals

lemma test_add_comm_1 : (7 : ENNReal) + 8 = 8 + 7 := by eq_as_reals

lemma test_add_comm_2 : (15 : ENNReal) + 25 = 25 + 15 := by eq_as_reals

lemma test_mul_comm_1 : (9 : ENNReal) * 10 = 10 * 9 := by eq_as_reals

lemma test_mul_comm_2 : (12 : ENNReal) * 13 = 13 * 12 := by eq_as_reals

lemma test_mixed_assoc_comm_1 : (1 : ENNReal) + 2 + 3 + 4 = 4 + 3 + 2 + 1 := by eq_as_reals

lemma test_mixed_assoc_comm_2 : (2 : ENNReal) * 3 * 4 * 5 = 5 * 4 * 3 * 2 := by eq_as_reals

end AssociativityTests

section MoreArithmeticTests

lemma test_nested_addition_1 : (((1 : ENNReal) + 2) + 3) + 4 = 10 := by eq_as_reals

lemma test_nested_addition_2 : ((((2 : ENNReal) + 3) + 4) + 5) + 6 = 20 := by eq_as_reals

lemma test_nested_multiplication_1 : (((2 : ENNReal) * 3) * 4) = 24 := by eq_as_reals

lemma test_nested_multiplication_2 : ((2 : ENNReal) * 3) * (4 * 5) = 120 := by eq_as_reals

lemma test_mixed_nested_1 : ((2 : ENNReal) + 3) * (4 + 1) = 25 := by eq_as_reals

lemma test_mixed_nested_2 : ((1 : ENNReal) + 1) * ((2 + 2) + 1) = 10 := by eq_as_reals

lemma test_mixed_nested_3 : (((3 : ENNReal) + 2) + 1) * (2 + 0) = 12 := by eq_as_reals

lemma test_nested_parens_2 : (((1 : ENNReal) * 2) * 3) * 4 = 24 := by eq_as_reals

end MoreArithmeticTests

section SequenceTests

lemma test_arithmetic_sequence_1 : (1 : ENNReal) + 2 + 3 + 4 + 5 = 15 := by eq_as_reals

lemma test_arithmetic_sequence_2 : (10 : ENNReal) + 20 + 30 + 40 + 50 = 150 := by eq_as_reals

lemma test_arithmetic_sequence_3 : (2 : ENNReal) + 4 + 6 + 8 + 10 = 30 := by eq_as_reals

lemma test_powers_of_two_sum : (1 : ENNReal) + 2 + 4 + 8 + 16 = 31 := by eq_as_reals

lemma test_powers_of_three_sum : (1 : ENNReal) + 3 + 9 + 27 = 40 := by eq_as_reals

lemma test_square_numbers_1 : (1 : ENNReal) + 4 + 9 + 16 = 30 := by eq_as_reals

lemma test_square_numbers_2 : (1 : ENNReal) + 4 + 9 + 16 + 25 = 55 := by eq_as_reals

lemma test_triangular_1 : (1 : ENNReal) + 3 + 6 + 10 = 20 := by eq_as_reals

lemma test_triangular_2 : (1 : ENNReal) + 3 + 6 + 10 + 15 = 35 := by eq_as_reals

end SequenceTests

section PatternTests

lemma test_fibonacci_1 : (1 : ENNReal) + 1 + 2 + 3 + 5 = 12 := by eq_as_reals

lemma test_fibonacci_2 : (1 : ENNReal) + 1 + 2 + 3 + 5 + 8 = 20 := by eq_as_reals

lemma test_fibonacci_3 : (1 : ENNReal) + 1 + 2 + 3 + 5 + 8 + 13 = 33 := by eq_as_reals

lemma test_alternating_1 : (1 : ENNReal) + 3 + 5 + 7 + 9 = 25 := by eq_as_reals

lemma test_alternating_2 : (2 : ENNReal) + 4 + 6 + 8 + 10 = 30 := by eq_as_reals

lemma test_alternating_3 : (10 : ENNReal) + 30 + 50 + 70 = 160 := by eq_as_reals

lemma test_doubling_1 : (1 : ENNReal) + 2 + 4 + 8 = 15 := by eq_as_reals

lemma test_doubling_2 : (3 : ENNReal) + 6 + 12 + 24 = 45 := by eq_as_reals

lemma test_doubling_3 : (5 : ENNReal) + 10 + 20 + 40 = 75 := by eq_as_reals

end PatternTests

section ParenthesesTests

lemma test_parens_1 : ((5 : ENNReal) + 3) * 2 = 16 := by eq_as_reals

lemma test_parens_2 : (7 : ENNReal) + (4 * 3) = 19 := by eq_as_reals

lemma test_parens_3 : ((10 : ENNReal) + 0) + 5 = 15 := by eq_as_reals

lemma test_nested_parens_1 : (((2 : ENNReal) + 3) + 4) = 9 := by eq_as_reals

lemma test_nested_parens_3 : ((((5 : ENNReal) + 1) + 2) + 3) = 11 := by eq_as_reals

lemma test_complex_parens_1 : ((2 : ENNReal) + 3) * ((4 + 5) + 6) = 75 := by eq_as_reals

lemma test_complex_parens_2 : ((1 : ENNReal) + (2 + 3)) + ((4 + 5) + 6) = 21 := by eq_as_reals

lemma test_complex_parens_3 : (((7 : ENNReal) + 8) + 9) + (((10 + 11) + 12) + 13) = 70 := by eq_as_reals

end ParenthesesTests

section MixedOperationTests

lemma test_triple_1 : (2 : ENNReal) + 3 * 4 / 1 = 14 := by eq_as_reals

lemma test_triple_2 : (5 : ENNReal) * 6 + 7 / 1 = 37 := by eq_as_reals

lemma test_triple_3 : (8 : ENNReal) / 1 + 9 * 2 = 26 := by eq_as_reals

lemma test_quadruple_1 : (1 : ENNReal) + 2 * 3 + 4 / 1 = 11 := by eq_as_reals

lemma test_quadruple_2 : (2 : ENNReal) * 3 + 4 * 5 / 1 = 26 := by eq_as_reals

lemma test_quadruple_3 : (10 : ENNReal) / 1 + 20 / 1 + 30 = 60 := by eq_as_reals

lemma test_complex_mixed_1 : ((2 : ENNReal) + 3) * 4 + (5 * 6) / 1 = 50 := by eq_as_reals

lemma test_complex_mixed_2 : ((7 : ENNReal) * 8) + (9 + 10) / 1 = 75 := by eq_as_reals

lemma test_complex_mixed_3 : (((1 : ENNReal) + 2) * 3 + 4) * 5 / 1 = 65 := by eq_as_reals

lemma test_mixed_demo_1 : (2 : ENNReal) + 3 * 4 = 14 := by eq_as_reals

lemma test_mixed_demo_2 : (5 : ENNReal) * 2 + 6 = 16 := by eq_as_reals

lemma test_mixed_demo_3 : (8 : ENNReal) / 1 + 9 = 17 := by eq_as_reals

end MixedOperationTests