import ENNRealArith.AdvancedSolver

open ENNReal

-- Test to see what's happening with the goal
lemma test_debug : (12 : ENNReal) / 3 / 2 = 2 := by
  -- First, let's see what norm_num does
  norm_num
  -- Now the goal should be 4 / 2 = 2
  sorry