import ENNRealArith.Basic
open ENNReal

-- Test the main ennreal_arith tactic
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_arith

-- Test ennreal_basic_simp alone
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_basic_simp

-- Test if simp can handle it
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  simp

-- Test if norm_num can handle it  
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  norm_num

-- Test the pattern step by step
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  -- Step 1: simplify + 0
  rw [add_zero]
  -- Step 2: add fractions
  -- ???
  sorry