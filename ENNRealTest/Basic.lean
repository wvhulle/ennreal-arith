import ENNRealArith

open ENNReal



-- set_option trace.ENNRealArith.conversion true in
lemma test_solve_as_real_inverse_1 : (5 : ENNReal)⁻¹ = 1 / 5 := by solve_as_real



lemma test_fraction_chain_1 : (12 : ENNReal) / 3 / 2 = 2 := by
  calc 12 / 3 / 2
  _ = (ENNReal.ofReal 12) / (ENNReal.ofReal 3) /  (ENNReal.ofReal 2) := by
    rw [<- ENNReal.ofReal_toReal (by norm_num : (12 : ENNReal) ≠ ⊤)]
    rw [<- ENNReal.ofReal_toReal (by norm_num : (3 : ENNReal) ≠ ⊤)]
    rw [<- ENNReal.ofReal_toReal (by norm_num : (2 : ENNReal) ≠ ⊤)]
    exact rfl
  _ = ((ENNReal.ofReal 12) / (ENNReal.ofReal 3)) /  (ENNReal.ofReal 2) := by
    exact rfl
  _ = ( ENNReal.ofReal ( 12 / 3)) / (ENNReal.ofReal 2) := by
    rw [ENNReal.ofReal_div_of_pos]
    norm_num
  _ =  ENNReal.ofReal (( 12 / 3) / 2) := by
    rw [<- ENNReal.ofReal_div_of_pos]
    · norm_num
  _ = ENNReal.ofReal (4 / 2) := by
    norm_num
  _ = ENNReal.ofReal 2 := by
    norm_num
  _ = 2 := by
    norm_num

lemma test_fraction_chain_1_auto : (12 : ENNReal) / 3 / 2 = 2 := by
  solve_as_real


lemma test_large_fraction_3 : (5000 : ENNReal) / 1000 * 3 = 15 := by
  solve_as_real


lemma test_nested_parens_2 : (((1 : ENNReal) * 2) * 3) * 4 = 24 := by solve_as_real


lemma test_advanced_basic : (2 : ENNReal) + 3 = 5 := by solve_as_real

-- lemma test_advanced_multiplication : (2 : ENNReal) * 3 * 4 = 24 := by ennreal_arith_advanced

-- lemma test_advanced_zero_handling : (5 : ENNReal) + 0 * 100 = 5 := by ennreal_arith_advanced

-- end BasicAdvancedTests

-- section ComplexNestedTests

-- -- Deep nesting tests
-- lemma test_deeply_nested_addition_1 :
--   ((((1 : ENNReal) + 2) + 3) + ((4 + 5) + 6)) = 21 := by ennreal_arith_advanced

-- lemma test_deeply_nested_addition_2 :
--   (((1 : ENNReal) + (2 + 3)) + ((4 + 5) + (6 + 7))) = 28 := by ennreal_arith_advanced

-- -- These require more sophisticated handling - demonstrates current limits
-- -- lemma test_deeply_nested_multiplication_1 :
-- --   (((2 : ENNReal) * 3) * 4) * ((5 * 6) * 7) = 2520 := by ennreal_arith_advanced

-- lemma test_deeply_nested_multiplication_simpler :
--   ((2 : ENNReal) * 3) * ((4 * 5) * 6) = 720 := by ennreal_arith_advanced

-- -- Mixed operation nesting
-- lemma test_mixed_nested_operations_1 :
--   ((2 : ENNReal) + 3) * ((4 + 1) * (6 + 0)) = 150 := by ennreal_arith_advanced

-- lemma test_mixed_nested_operations_2 :
--   (((1 : ENNReal) + 2) + 3) * (((4 + 5) + 6) + 7) = 132 := by ennreal_arith_advanced

-- -- Extremely deep nesting hits current solver limits
-- -- lemma test_extremely_deep_nesting :
-- --   ((((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) + (((1 + 1) + (1 + 1)) + ((1 + 1) + (1 + 1)))) = 14 := by ennreal_arith_advanced

-- -- Test moderately deep nesting that works
-- lemma test_moderately_deep_nesting :
--   (((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) = 7 := by ennreal_arith_advanced

-- end ComplexNestedTests

-- section LargeNumberTests

-- -- Large arithmetic chains
-- lemma test_long_addition_chain :
--   (1 : ENNReal) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by ennreal_arith_advanced

-- lemma test_long_multiplication_chain :
--   (1 : ENNReal) * 2 * 3 * 4 * 5 = 120 := by ennreal_arith_advanced

-- -- Large numbers
-- lemma test_large_number_arithmetic :
--   (100 : ENNReal) + 200 + 300 + 400 + 500 = 1500 := by ennreal_arith_advanced

-- lemma test_very_large_arithmetic :
--   (1000 : ENNReal) + 2000 + 3000 = 6000 := by ennreal_arith_advanced

-- end LargeNumberTests

-- section DistributivityTests

-- -- Complex distributivity patterns
-- lemma test_distributivity_complex_1 :
--   ((2 : ENNReal) + 3) * (4 + 5) = 2 * 4 + 2 * 5 + 3 * 4 + 3 * 5 := by ennreal_arith_advanced

-- lemma test_distributivity_complex_2 :
--   ((1 : ENNReal) + 2) * ((3 + 4) + (5 + 6)) = 3 * 18 := by ennreal_arith_advanced

-- lemma test_distributivity_with_zero :
--   ((5 : ENNReal) + 0) * ((3 + 0) + (2 + 0)) = 25 := by ennreal_arith_advanced

-- end DistributivityTests

-- section AssociativityTests

-- -- Associativity with complex expressions
-- lemma test_associativity_addition_complex :
--   ((1 : ENNReal) + (2 + 3)) + (4 + 5) = (1 + 2) + ((3 + 4) + 5) := by ennreal_arith_advanced

-- lemma test_associativity_multiplication_complex :
--   ((2 : ENNReal) * (3 * 4)) * (5 * 6) = (2 * 3) * ((4 * 5) * 6) := by ennreal_arith_advanced

-- -- Mixed associativity
-- lemma test_mixed_associativity :
--   ((1 : ENNReal) + 2) * ((3 + 4) * 5) = 1 * 3 * 5 + 1 * 4 * 5 + 2 * 3 * 5 + 2 * 4 * 5 := by ennreal_arith_advanced

-- end AssociativityTests

-- -- =============================================
-- -- STRESS TESTS FOR EXTREME COMPLEXITY
-- -- =============================================

-- section StressTests

-- -- Maximum complexity tests
-- lemma test_stress_extremely_nested :
--   ((((((2 : ENNReal) + 3) + 4) + 5) + 6) + 7) + ((((8 + 9) + 10) + 11) + 12) = 77 := by ennreal_arith_advanced

-- lemma test_stress_mixed_operations :
--   (((2 : ENNReal) + 3) * 4 + (5 * 6) + ((7 + 8) * 9)) + 0 = 185 := by ennreal_arith_advanced

-- -- Fibonacci-like recursive patterns
-- lemma test_stress_fibonacci_pattern :
--   let a := (1 : ENNReal)
--   let b := (1 : ENNReal)
--   let c := a + b
--   let d := b + c
--   let e := c + d
--   let f := d + e
--   a + b + c + d + e + f = 20 := by ennreal_arith_advanced

-- -- Factorial-like patterns
-- lemma test_stress_factorial_pattern :
--   (1 : ENNReal) * (1 + 1) * (1 + 1 + 1) * (1 + 1 + 1 + 1) * (1 + 1 + 1 + 1 + 1) = 120 := by ennreal_arith_advanced

-- end StressTests

-- section FractionArithmeticTests

-- -- Test that basic arithmetic still works
-- lemma test_basic_addition_check : (2 : ENNReal) + 3 = 5 := by ennreal_arith_advanced

-- lemma test_basic_multiplication_check : (2 : ENNReal) * 3 = 6 := by ennreal_arith_advanced

-- -- Now try division tests step by step
-- lemma test_fraction_div_one : (7 : ENNReal) / 1 = 7 := by ennreal_arith_advanced

-- -- Division by self cases (these should work from ImprovedSolver)
-- lemma test_fraction_div_self_1 : (5 : ENNReal) / 5 = 1 := by ennreal_arith_advanced

-- -- More division by self tests
-- lemma test_fraction_div_self_2 : (17 : ENNReal) / 17 = 1 := by ennreal_arith_advanced

-- lemma test_fraction_div_self_3 : (100 : ENNReal) / 100 = 1 := by ennreal_arith_advanced

-- -- Division by 1 tests
-- lemma test_fraction_div_one_2 : (15 : ENNReal) / 1 = 15 := by ennreal_arith_advanced

-- lemma test_fraction_div_one_3 : (42 : ENNReal) / 1 = 42 := by ennreal_arith_advanced

-- end FractionArithmeticTests

-- -- =============================================
-- -- ADDITIONAL ARITHMETIC TESTS
-- -- =============================================

-- section MoreArithmeticTests

-- -- Large number tests
-- lemma test_large_addition_1 : (100 : ENNReal) + 200 + 300 = 600 := by ennreal_arith_advanced

-- lemma test_large_addition_2 : (1000 : ENNReal) + 2000 + 3000 + 4000 = 10000 := by ennreal_arith_advanced

-- lemma test_large_multiplication_1 : (100 : ENNReal) * 5 = 500 := by ennreal_arith_advanced

-- lemma test_large_multiplication_2 : (50 : ENNReal) * 20 = 1000 := by ennreal_arith_advanced

-- -- Zero patterns
-- lemma test_zero_pattern_1 : (0 : ENNReal) + 0 + 0 + 5 = 5 := by ennreal_arith_advanced

-- lemma test_zero_pattern_2 : (10 : ENNReal) * 0 + 7 = 7 := by ennreal_arith_advanced

-- lemma test_zero_pattern_3 : (0 : ENNReal) * 100 + 8 * 1 = 8 := by ennreal_arith_advanced

-- -- One patterns
-- lemma test_one_pattern_1 : (15 : ENNReal) * 1 * 1 = 15 := by ennreal_arith_advanced

-- lemma test_one_pattern_2 : (7 : ENNReal) * 1 + 3 * 1 = 10 := by ennreal_arith_advanced

-- -- Complex nested addition
-- lemma test_nested_addition_1 : (((1 : ENNReal) + 2) + 3) + 4 = 10 := by ennreal_arith_advanced

-- lemma test_nested_addition_2 : ((((2 : ENNReal) + 3) + 4) + 5) + 6 = 20 := by ennreal_arith_advanced

-- -- Complex nested multiplication
-- lemma test_nested_multiplication_1 : (((2 : ENNReal) * 3) * 4) = 24 := by ennreal_arith_advanced

-- lemma test_nested_multiplication_2 : ((2 : ENNReal) * 3) * (4 * 5) = 120 := by ennreal_arith_advanced

-- -- Mixed nested operations
-- lemma test_mixed_nested_1 : ((2 : ENNReal) + 3) * (4 + 1) = 25 := by ennreal_arith_advanced

-- lemma test_mixed_nested_2 : ((1 : ENNReal) + 1) * ((2 + 2) + 1) = 10 := by ennreal_arith_advanced

-- lemma test_mixed_nested_3 : (((3 : ENNReal) + 2) + 1) * (2 + 0) = 12 := by ennreal_arith_advanced

-- end MoreArithmeticTests

-- -- =============================================
-- -- POLYNOMIAL AND DISTRIBUTIVE TESTS
-- -- =============================================

-- section PolynomialTests

-- -- Distributivity patterns
-- lemma test_distributive_1 : (2 : ENNReal) * (3 + 4) = 2 * 3 + 2 * 4 := by ennreal_arith_advanced

-- lemma test_distributive_2 : (5 : ENNReal) * (6 + 7) = 5 * 6 + 5 * 7 := by ennreal_arith_advanced

-- lemma test_distributive_3 : (1 : ENNReal) * (10 + 20 + 30) = 1 * 10 + 1 * 20 + 1 * 30 := by ennreal_arith_advanced

-- -- Left distributivity
-- lemma test_left_distributive_1 : ((3 : ENNReal) + 4) * 5 = 3 * 5 + 4 * 5 := by ennreal_arith_advanced

-- lemma test_left_distributive_2 : ((7 : ENNReal) + 8) * 9 = 7 * 9 + 8 * 9 := by ennreal_arith_advanced

-- -- Complex distributive patterns
-- lemma test_complex_distributive_1 : (2 : ENNReal) * (3 + 4) + 5 * (6 + 7) = 14 + 65 := by ennreal_arith_advanced

-- lemma test_complex_distributive_2 : (1 : ENNReal) * (2 + 3) * (4 + 5) = 5 * 9 := by ennreal_arith_advanced

-- -- Factoring patterns (reverse distributivity)
-- lemma test_factoring_1 : (6 : ENNReal) + 9 = 3 * (2 + 3) := by ennreal_arith_advanced

-- lemma test_factoring_2 : (10 : ENNReal) + 15 = 5 * (2 + 3) := by ennreal_arith_advanced

-- lemma test_factoring_3 : (12 : ENNReal) + 18 + 24 = 6 * (2 + 3 + 4) := by ennreal_arith_advanced

-- end PolynomialTests

-- -- =============================================
-- -- ASSOCIATIVITY AND COMMUTATIVITY TESTS
-- -- =============================================

-- section AssociativityCommutativeTests

-- -- Addition associativity
-- lemma test_add_assoc_1 : ((1 : ENNReal) + 2) + 3 = 1 + (2 + 3) := by ennreal_arith_advanced

-- lemma test_add_assoc_2 : ((5 : ENNReal) + 6) + 7 = 5 + (6 + 7) := by ennreal_arith_advanced

-- lemma test_add_assoc_3 : (((10 : ENNReal) + 11) + 12) + 13 = 10 + ((11 + 12) + 13) := by ennreal_arith_advanced

-- -- Multiplication associativity
-- lemma test_mul_assoc_1 : ((2 : ENNReal) * 3) * 4 = 2 * (3 * 4) := by ennreal_arith_advanced

-- lemma test_mul_assoc_2 : ((5 : ENNReal) * 6) * 7 = 5 * (6 * 7) := by ennreal_arith_advanced

-- -- Addition commutativity
-- lemma test_add_comm_1 : (7 : ENNReal) + 8 = 8 + 7 := by ennreal_arith_advanced

-- lemma test_add_comm_2 : (15 : ENNReal) + 25 = 25 + 15 := by ennreal_arith_advanced

-- -- Multiplication commutativity
-- lemma test_mul_comm_1 : (9 : ENNReal) * 10 = 10 * 9 := by ennreal_arith_advanced

-- lemma test_mul_comm_2 : (12 : ENNReal) * 13 = 13 * 12 := by ennreal_arith_advanced

-- -- Mixed associativity and commutativity
-- lemma test_mixed_assoc_comm_1 : (1 : ENNReal) + 2 + 3 + 4 = 4 + 3 + 2 + 1 := by ennreal_arith_advanced

-- lemma test_mixed_assoc_comm_2 : (2 : ENNReal) * 3 * 4 * 5 = 5 * 4 * 3 * 2 := by ennreal_arith_advanced

-- end AssociativityCommutativeTests

-- -- =============================================
-- -- NUMERICAL SEQUENCES AND PATTERNS
-- -- =============================================

-- section SequenceTests

-- -- Arithmetic sequences
-- lemma test_arithmetic_sequence_1 : (1 : ENNReal) + 2 + 3 + 4 + 5 = 15 := by ennreal_arith_advanced

-- lemma test_arithmetic_sequence_2 : (10 : ENNReal) + 20 + 30 + 40 + 50 = 150 := by ennreal_arith_advanced

-- lemma test_arithmetic_sequence_3 : (2 : ENNReal) + 4 + 6 + 8 + 10 = 30 := by ennreal_arith_advanced

-- -- Geometric-like patterns
-- lemma test_powers_of_two_sum : (1 : ENNReal) + 2 + 4 + 8 + 16 = 31 := by ennreal_arith_advanced

-- lemma test_powers_of_three_sum : (1 : ENNReal) + 3 + 9 + 27 = 40 := by ennreal_arith_advanced

-- -- Square numbers
-- lemma test_square_numbers_1 : (1 : ENNReal) + 4 + 9 + 16 = 30 := by ennreal_arith_advanced

-- lemma test_square_numbers_2 : (1 : ENNReal) + 4 + 9 + 16 + 25 = 55 := by ennreal_arith_advanced

-- -- Triangular numbers
-- lemma test_triangular_1 : (1 : ENNReal) + 3 + 6 + 10 = 20 := by ennreal_arith_advanced

-- lemma test_triangular_2 : (1 : ENNReal) + 3 + 6 + 10 + 15 = 35 := by ennreal_arith_advanced

-- end SequenceTests

-- -- =============================================
-- -- EXTREMELY LARGE NUMBER TESTS
-- -- =============================================

-- section LargeNumberTests

-- -- Very large additions
-- lemma test_large_1 : (1000 : ENNReal) + 2000 + 3000 + 4000 + 5000 = 15000 := by ennreal_arith_advanced

-- lemma test_large_2 : (10000 : ENNReal) + 20000 + 30000 = 60000 := by ennreal_arith_advanced

-- lemma test_large_3 : (50000 : ENNReal) + 50000 = 100000 := by ennreal_arith_advanced

-- -- Large multiplications
-- lemma test_large_mul_1 : (1000 : ENNReal) * 10 = 10000 := by ennreal_arith_advanced

-- lemma test_large_mul_2 : (500 : ENNReal) * 20 = 10000 := by ennreal_arith_advanced

-- lemma test_large_mul_3 : (250 : ENNReal) * 40 = 10000 := by ennreal_arith_advanced

-- -- Mixed large operations
-- lemma test_large_mixed_1 : (1000 : ENNReal) + 2000 * 3 = 7000 := by ennreal_arith_advanced

-- lemma test_large_mixed_2 : (500 : ENNReal) * 2 + 3000 = 4000 := by ennreal_arith_advanced

-- lemma test_large_mixed_3 : (100 : ENNReal) * 10 + 200 * 5 = 2000 := by ennreal_arith_advanced

-- end LargeNumberTests

-- -- =============================================
-- -- EDGE CASE AND BOUNDARY TESTS
-- -- =============================================

-- section EdgeCaseTests

-- -- Single operand tests
-- lemma test_single_1 : (42 : ENNReal) = 42 := by ennreal_arith_advanced

-- lemma test_single_2 : (0 : ENNReal) = 0 := by ennreal_arith_advanced

-- lemma test_single_3 : (1 : ENNReal) = 1 := by ennreal_arith_advanced

-- -- Identity operations
-- lemma test_identity_1 : (7 : ENNReal) + 0 = 7 := by ennreal_arith_advanced

-- lemma test_identity_2 : (9 : ENNReal) * 1 = 9 := by ennreal_arith_advanced

-- lemma test_identity_3 : (15 : ENNReal) / 1 = 15 := by ennreal_arith_advanced

-- -- Zero operations
-- lemma test_zero_1 : (0 : ENNReal) + 15 = 15 := by ennreal_arith_advanced

-- lemma test_zero_2 : (0 : ENNReal) * 99 = 0 := by ennreal_arith_advanced

-- lemma test_zero_3 : (25 : ENNReal) * 0 = 0 := by ennreal_arith_advanced

-- -- Multiple zeros
-- lemma test_multiple_zeros_1 : (0 : ENNReal) + 0 + 0 = 0 := by ennreal_arith_advanced

-- lemma test_multiple_zeros_2 : (0 : ENNReal) * 0 * 0 = 0 := by ennreal_arith_advanced

-- lemma test_multiple_zeros_3 : (0 : ENNReal) + 0 + 0 + 0 + 0 = 0 := by ennreal_arith_advanced

-- -- Multiple ones
-- lemma test_multiple_ones_1 : (1 : ENNReal) * 1 * 1 = 1 := by ennreal_arith_advanced

-- lemma test_multiple_ones_2 : (1 : ENNReal) + 1 + 1 = 3 := by ennreal_arith_advanced

-- lemma test_multiple_ones_3 : (1 : ENNReal) * 1 * 1 * 1 * 1 = 1 := by ennreal_arith_advanced

-- end EdgeCaseTests

-- -- =============================================
-- -- CHAIN OPERATION TESTS
-- -- =============================================

-- section ChainOperationTests

-- -- Long addition chains
-- lemma test_chain_add_1 : (1 : ENNReal) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 10 := by ennreal_arith_advanced

-- lemma test_chain_add_2 : (2 : ENNReal) + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 20 := by ennreal_arith_advanced

-- lemma test_chain_add_3 : (5 : ENNReal) + 5 + 5 + 5 + 5 + 5 + 5 + 5 = 40 := by ennreal_arith_advanced

-- -- Long multiplication chains
-- lemma test_chain_mul_1 : (2 : ENNReal) * 2 * 2 * 2 = 16 := by ennreal_arith_advanced

-- lemma test_chain_mul_2 : (3 : ENNReal) * 3 * 3 = 27 := by ennreal_arith_advanced

-- lemma test_chain_mul_3 : (1 : ENNReal) * 2 * 3 * 4 * 5 = 120 := by ennreal_arith_advanced

-- -- Mixed operation chains
-- lemma test_chain_mixed_1 : (2 : ENNReal) + 3 * 4 + 5 = 19 := by ennreal_arith_advanced

-- lemma test_chain_mixed_2 : (1 : ENNReal) * 2 + 3 * 4 + 5 * 6 = 44 := by ennreal_arith_advanced

-- lemma test_chain_mixed_3 : (10 : ENNReal) + 20 * 2 + 30 / 1 = 80 := by ennreal_arith_advanced

-- end ChainOperationTests

-- -- =============================================
-- -- PARENTHESES AND PRECEDENCE TESTS
-- -- =============================================

-- section ParenthesesTests

-- -- Simple parentheses
-- lemma test_parens_1 : ((5 : ENNReal) + 3) * 2 = 16 := by ennreal_arith_advanced

-- lemma test_parens_2 : (7 : ENNReal) + (4 * 3) = 19 := by ennreal_arith_advanced

-- lemma test_parens_3 : ((10 : ENNReal) + 0) + 5 = 15 := by ennreal_arith_advanced

-- -- Nested parentheses
-- lemma test_nested_parens_1 : (((2 : ENNReal) + 3) + 4) = 9 := by ennreal_arith_advanced



lemma test_nested_parens_3 : ((((5 : ENNReal) + 1) + 2) + 3) = 11 := by solve_as_real

-- -- Complex parentheses
-- lemma test_complex_parens_1 : ((2 : ENNReal) + 3) * ((4 + 5) + 6) = 75 := by ennreal_arith_advanced

-- lemma test_complex_parens_2 : ((1 : ENNReal) + (2 + 3)) + ((4 + 5) + 6) = 21 := by ennreal_arith_advanced

-- lemma test_complex_parens_3 : (((7 : ENNReal) + 8) + 9) + (((10 + 11) + 12) + 13) = 70 := by ennreal_arith_advanced

-- end ParenthesesTests

-- -- =============================================
-- -- MIXED COMPLEX EXPRESSIONS
-- -- =============================================

-- section MixedComplexTests

-- -- Triple operations
-- lemma test_triple_1 : (2 : ENNReal) + 3 * 4 / 1 = 14 := by ennreal_arith_advanced

-- lemma test_triple_2 : (5 : ENNReal) * 6 + 7 / 1 = 37 := by ennreal_arith_advanced

-- lemma test_triple_3 : (8 : ENNReal) / 1 + 9 * 2 = 26 := by ennreal_arith_advanced

-- -- Quadruple operations
-- lemma test_quadruple_1 : (1 : ENNReal) + 2 * 3 + 4 / 1 = 11 := by ennreal_arith_advanced

-- lemma test_quadruple_2 : (2 : ENNReal) * 3 + 4 * 5 / 1 = 26 := by ennreal_arith_advanced

-- lemma test_quadruple_3 : (10 : ENNReal) / 1 + 20 / 1 + 30 = 60 := by ennreal_arith_advanced

-- -- Complex mixed with parentheses
-- lemma test_complex_mixed_1 : ((2 : ENNReal) + 3) * 4 + (5 * 6) / 1 = 50 := by ennreal_arith_advanced

-- lemma test_complex_mixed_2 : ((7 : ENNReal) * 8) + (9 + 10) / 1 = 75 := by ennreal_arith_advanced

-- lemma test_complex_mixed_3 : (((1 : ENNReal) + 2) * 3 + 4) * 5 / 1 = 65 := by ennreal_arith_advanced

-- end MixedComplexTests

-- -- =============================================
-- -- PATTERN RECOGNITION TESTS
-- -- =============================================

-- section PatternTests

-- -- Fibonacci-like patterns
-- lemma test_fibonacci_1 : (1 : ENNReal) + 1 + 2 + 3 + 5 = 12 := by ennreal_arith_advanced

-- lemma test_fibonacci_2 : (1 : ENNReal) + 1 + 2 + 3 + 5 + 8 = 20 := by ennreal_arith_advanced

-- lemma test_fibonacci_3 : (1 : ENNReal) + 1 + 2 + 3 + 5 + 8 + 13 = 33 := by ennreal_arith_advanced

-- -- Alternating patterns
-- lemma test_alternating_1 : (1 : ENNReal) + 3 + 5 + 7 + 9 = 25 := by ennreal_arith_advanced

-- lemma test_alternating_2 : (2 : ENNReal) + 4 + 6 + 8 + 10 = 30 := by ennreal_arith_advanced

-- lemma test_alternating_3 : (10 : ENNReal) + 30 + 50 + 70 = 160 := by ennreal_arith_advanced

-- -- Doubling patterns
-- lemma test_doubling_1 : (1 : ENNReal) + 2 + 4 + 8 = 15 := by ennreal_arith_advanced

-- lemma test_doubling_2 : (3 : ENNReal) + 6 + 12 + 24 = 45 := by ennreal_arith_advanced

-- lemma test_doubling_3 : (5 : ENNReal) + 10 + 20 + 40 = 75 := by ennreal_arith_advanced

-- end PatternTests

-- -- =============================================
-- -- FINAL STRESS TESTS
-- -- =============================================

-- section FinalStressTests

-- -- Maximum nesting that works
-- lemma test_max_nesting_1 : ((((((1 : ENNReal) + 1) + 1) + 1) + 1) + 1) + 1 = 7 := by ennreal_arith_advanced

-- lemma test_max_nesting_2 : ((((((2 : ENNReal) * 2) + 1) + 1) + 1) + 1) + 1 = 9 := by ennreal_arith_advanced

-- lemma test_max_nesting_3 : (((((((3 : ENNReal) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 10 := by ennreal_arith_advanced

-- -- Very long chains
-- lemma test_very_long_1 : (1 : ENNReal) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 15 := by ennreal_arith_advanced

-- lemma test_very_long_2 : (2 : ENNReal) + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = 26 := by ennreal_arith_advanced

-- lemma test_very_long_3 : (1 : ENNReal) * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 * 1 = 1 := by ennreal_arith_advanced

-- -- Complex expressions combining all patterns
-- lemma test_ultimate_1 : ((((2 : ENNReal) + 3) * 4) + ((5 + 6) * 7)) + (((8 + 9) + 10) * 0) = 97 := by ennreal_arith_advanced

-- lemma test_ultimate_2 : (((1 : ENNReal) + 2 + 3) * (4 + 5)) + (6 * 7) = 96 := by ennreal_arith_advanced

-- lemma test_ultimate_3 : ((((10 : ENNReal) + 20) + 30) + (((40 + 50) + 60) + 70)) + 0 = 280 := by ennreal_arith_advanced

-- -- Final verification that basic operations still work after all additions
-- lemma test_final_basic_1 : (2 : ENNReal) + 2 = 4 := by ennreal_arith_advanced

-- lemma test_final_basic_2 : (3 : ENNReal) * 3 = 9 := by ennreal_arith_advanced

-- lemma test_final_basic_3 : (10 : ENNReal) / 10 = 1 := by ennreal_arith_advanced

-- end FinalStressTests

-- -- =============================================
-- -- INVERSE AND MIXED OPERATOR DEVELOPMENT
-- -- =============================================

-- /-!
-- ## Enhanced Inverse and Mixed Operator Support

-- ### Inverse Support Added to Solver:
-- The `solveAdvancedFractions` function now includes:
-- - `repeat rw [inv_eq_one_div]; norm_num` - Like Basic.lean
-- - `simp only [inv_eq_one_div]; norm_num` - Direct inverse handling
-- - `simp only [div_eq_mul_inv, inv_eq_one_div]; field_simp; norm_num` - Complex patterns

-- ### Working Inverse Tests (Basic Level):
-- These demonstrate the foundation for inverse arithmetic:
-- - Basic conversion: `x⁻¹ = 1/x`
-- - Simple inverse addition patterns
-- - Integration with existing fraction handling

-- ### Mixed Operator Tests:
-- The current solver successfully handles:
-- - Basic mixed chains: `a + b * c + d`
-- - Simple nesting: `(a + b) * c`
-- - Mixed operations with division by 1

-- ### Future Development Areas:
-- For full inverse and complex mixed operator support, the solver would need:
-- 1. Enhanced inverse multiplication: `x⁻¹ * x = 1`
-- 2. Complex inverse combinations: `(x⁻¹ + y⁻¹) * z`
-- 3. Multi-level nesting with varied operators
-- 4. Advanced operator precedence chains

-- The current implementation provides the foundation for these capabilities.
-- -/

-- section InverseOperationTests

-- -- Basic inverse tests (foundation working)
-- lemma test_inverse_basic_1 : (5 : ENNReal)⁻¹ = 1 / 5 := by ennreal_arith_advanced

-- lemma test_inverse_basic_2 : (10 : ENNReal)⁻¹ = 1 / 10 := by ennreal_arith_advanced

-- lemma test_inverse_basic_3 : (2 : ENNReal)⁻¹ = 1 / 2 := by ennreal_arith_advanced

-- end InverseOperationTests

-- section MultiLevelMixedOperatorTests

-- -- Working mixed operator demonstrations
-- lemma test_mixed_demo_1 : (2 : ENNReal) + 3 * 4 = 14 := by ennreal_arith_advanced

-- lemma test_mixed_demo_2 : (5 : ENNReal) * 2 + 6 = 16 := by ennreal_arith_advanced

-- lemma test_mixed_demo_3 : (8 : ENNReal) / 1 + 9 = 17 := by ennreal_arith_advanced

-- end MultiLevelMixedOperatorTests

-- -- =============================================
-- -- FRACTION AND INVERSE STRESS TESTS
-- -- =============================================

-- section FractionInverseStressTests

-- -- Division stress tests
-- lemma test_div_stress_1 : (100 : ENNReal) / 1 / 1 / 1 / 1 / 1 = 100 := by ennreal_arith_advanced

-- lemma test_div_stress_2 : (50 : ENNReal) / 1 / 1 + 50 / 1 / 1 = 100 := by ennreal_arith_advanced

-- lemma test_div_stress_3 : (25 : ENNReal) / 1 * 4 / 1 = 100 := by ennreal_arith_advanced

-- -- Multiple division patterns
-- lemma test_multi_div_1 : ((20 : ENNReal) / 4) / 1 = 5 := by ennreal_arith_advanced

-- lemma test_multi_div_2 : (30 : ENNReal) / (6 / 1) = 5 := by ennreal_arith_advanced

lemma test_multi_div_3 : ((40 : ENNReal) / 8) + ((50 / 10)) = 10 := by solve_as_real

-- -- Chain of self-divisions
-- lemma test_self_div_chain_1 : (7 : ENNReal) / 7 / 1 = 1 := by ennreal_arith_advanced

-- lemma test_self_div_chain_2 : (9 : ENNReal) / 9 + 8 / 8 = 2 := by ennreal_arith_advanced



-- lemma test_self_div_chain_3 : (11 : ENNReal) / 11 * 5 / 5 = 1 := by
--   rw [ENNReal.div_self (by norm_num : (11 : ENNReal) ≠ 0) (by norm_num : (11 : ENNReal) ≠ ⊤)]
--   rw [mul_div_assoc]
--   rw [ENNReal.div_self (by norm_num : (5 : ENNReal) ≠ 0) (by norm_num : (5 : ENNReal) ≠ ⊤)]
--   norm_num


-- -- Inverse stress patterns (working with current solver)
-- lemma test_inverse_stress_1 : (3 : ENNReal)⁻¹ + (3 : ENNReal)⁻¹ = 2 * (3 : ENNReal)⁻¹ := by ennreal_arith_advanced

lemma test_inverse_stress_2 : (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = 3 * (4 : ENNReal)⁻¹ := by solve_as_real

-- -- Large number fraction stress
-- lemma test_large_fraction_1 : (1000 : ENNReal) / 100 = 10 := by ennreal_arith_advanced

-- lemma test_large_fraction_2 : (2000 : ENNReal) / 200 + 5 = 15 := by
--   solve_as_real






lemma test_fraction_chain_1_real : (12 : ENNReal) / 3 / 2 = 2 := by solve_as_real

-- -- Additional tests demonstrating solve_as_real capabilities
lemma test_solve_as_real_1 : (100 : ENNReal) / 10 = 10 := by solve_as_real

lemma test_solve_as_real_2 : (200 : ENNReal) / 50 * 2 = 8 := by solve_as_real

lemma test_solve_as_real_3 : (1500 : ENNReal) / 300 / 5 = 1 := by solve_as_real

-- -- Comprehensive inverse tests with solve_as_real


-- lemma test_solve_as_real_inverse_2 : (10 : ENNReal)⁻¹ * 10 = 1 := by solve_as_real

-- lemma test_solve_as_real_inverse_3 : 3 * (3 : ENNReal)⁻¹ = 1 := by solve_as_real

-- lemma test_solve_as_real_inverse_4 : (100 : ENNReal)⁻¹ + (100 : ENNReal)⁻¹ = 2 * (100 : ENNReal)⁻¹ := by ring_nf

-- lemma test_solve_as_real_inverse_5 : (7 : ENNReal)⁻¹ * 7 * 2 = 2 := by
--   rw [ENNReal.inv_mul_cancel]
--   · norm_num
--   · norm_num
--   · norm_num

-- lemma test_solve_as_real_inverse_6 : (6 : ENNReal)⁻¹ + 6 / 6 = (6 : ENNReal)⁻¹ + 1 := by solve_as_real

-- -- Additional inverse edge cases
-- lemma test_solve_as_real_inverse_large : (1000 : ENNReal)⁻¹ = 1 / 1000 := by solve_as_real

-- lemma test_solve_as_real_inverse_mixed : (50 : ENNReal)⁻¹ * 50 / 2 = 1 / 2 := by solve_as_real


-- lemma test_fraction_chain_2 : (24 : ENNReal) / 4 / 3 = 2 := by
--   rw [div_div]
--   · norm_num
--     rw [div_eq_iff]
--     · norm_num
--     · norm_num
--     · norm_num
--   · norm_num
--   · norm_num


-- lemma test_fraction_chain_3 : (60 : ENNReal) / 6 / 5 = 2 := by
--   rw [div_div]
--   · norm_num
--     rw [div_eq_iff]
--     · norm_num
--     · norm_num
--     · norm_num
--   · norm_num
--   · norm_num


-- -- Stress test with many operations
-- lemma test_many_ops_1 : (2 : ENNReal) / 1 + 3 / 1 + 4 / 1 + 5 / 1 = 14 := by ennreal_arith_advanced

-- lemma test_many_ops_2 : (10 : ENNReal) / 2 + 15 / 3 + 20 / 4 + 25 / 5 = 20 := by
--   repeat rw [add_assoc]
--   repeat
--     rw [add_mixed_denom]
--   rw [div_eq_iff]
--   repeat norm_num



-- lemma test_many_ops_3 : (6 : ENNReal) / 6 + 7 / 7 + 8 / 8 + 9 / 9 + 10 / 10 = 5 := by
--   repeat rw [add_assoc]
--   repeat
--     rw [add_mixed_denom]
--   rw [div_eq_iff]
--   repeat norm_num

-- -- Combined fraction and inverse stress
-- lemma test_combined_stress_1 : (6 : ENNReal)⁻¹ + 6 / 6 = (6 : ENNReal)⁻¹ + 1 := by
--   rw [ENNReal.div_self]
--   . norm_num
--   . norm_num

-- lemma test_combined_stress_2 : (8 : ENNReal)⁻¹ + 8 / 8 + 0 = (8 : ENNReal)⁻¹ + 1 := by
--   rw [ENNReal.div_self]
--   . norm_num
--   . norm_num
--   . norm_num

-- -- Maximum stress within solver capabilities
lemma test_max_stress_1 : ((((2 : ENNReal) / 1) + 3) / 1 + 4) / 1 = 9 := by solve_as_real

lemma test_max_stress_2 : (((5 : ENNReal)⁻¹ + (5 : ENNReal)⁻¹) + 0) + 0 = 2 * (5 : ENNReal)⁻¹ := by solve_as_real

lemma test_max_stress_3 : ((10 : ENNReal) / 10 + 20 / 20 + 30 / 30) * 2 = 6 := by
  solve_as_real

-- end FractionInverseStressTests
