import ENNRealArith.Basic
open ENNReal

-- Test the original problematic goal
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 1 / 6 := by
  ennreal_arith

-- Test just the basic pattern
example : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by 
  ennreal_arith

-- Test simplification
example : (3 : ENNReal) / 18 = 1 / 6 := by
  ennreal_arith