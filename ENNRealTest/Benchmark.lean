import ENNRealArith
import Mathlib.Tactic.Basic
open ENNReal

set_option profiler true

section BenchmarkTests

-- Simple baseline test
lemma benchmark_simple : (2 : ENNReal) + 3 = 5 := by eq_as_reals

-- Moderate complexity test
lemma benchmark_moderate :
  (((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) = 7 := by eq_as_reals

-- High complexity test
lemma benchmark_complex :
  (((((1 : ENNReal) + 1) + 1) + 1) + ((1 + 1) + 1)) + (((1 + 1) + (1 + 1)) + ((1 + 1) + (1 + 1))) = 15 := by eq_as_reals

-- Very long chain test  
lemma benchmark_long_chain :
  (1 : ENNReal) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 15 := by eq_as_reals

-- Deep nesting test
lemma benchmark_deep_nesting :
  ((((((1 : ENNReal) + 1) + 1) + 1) + 1) + 1) + 1 = 7 := by eq_as_reals

-- Large arithmetic test
lemma benchmark_large_numbers :
  (1000 : ENNReal) + 2000 + 3000 + 4000 + 5000 = 15000 := by eq_as_reals

-- Mixed operations test
lemma benchmark_mixed_ops :
  ((2 : ENNReal) + 3) * 4 + (5 * 6) / 1 = 50 := by eq_as_reals

-- Division chain test
lemma benchmark_division :
  (12 : ENNReal) / 3 / 2 = 2 := by eq_as_reals

-- Fibonacci pattern test
lemma benchmark_fibonacci :
  let a := (1 : ENNReal)
  let b := (1 : ENNReal)
  let c := a + b
  let d := b + c
  let e := c + d
  let f := d + e
  a + b + c + d + e + f = 20 := by eq_as_reals

end BenchmarkTests