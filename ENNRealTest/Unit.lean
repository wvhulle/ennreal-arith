
import ENNRealArith

open ENNReal

-- Helper lemma for 2/2 = 1
lemma two_div_two_eq_one : (2 : ENNReal) / 2 = 1 := by
  rw [ENNReal.div_self]
  · norm_num
  · norm_num



section DivSelfTests

example {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_div_self

example {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  apply ENNReal.div_self
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by assumption))
  · exact ENNReal.coe_ne_top

example {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by ennreal_div_self
example : (↑2 : ENNReal) / ↑2 = 1 := by
  ennreal_div_self

end DivSelfTests

section MulCancelTests

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel
example {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by ennreal_mul_cancel

example : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

example {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by ennreal_mul_cancel

end MulCancelTests

section MulDivAssocTests

example {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_mul_div_assoc
example {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by ennreal_mul_div_assoc
example : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by ennreal_mul_div_assoc
example {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by ennreal_mul_div_assoc
example {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by ennreal_mul_div_assoc

end MulDivAssocTests

section InvPatternTests

example {a b : ℕ} (_ha : a ≠ 0) : (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform
example {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform
example {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by simp only [inv_inv]
example {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by simp only [inv_eq_one_div]
example {a b c : ℕ} : (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by simp only [one_div, inv_inv, mul_div]

end InvPatternTests

section FractionAddTests

example : ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by ennreal_fraction_add
example : ((1 : ENNReal) + 2) / 18 = 3 / 18 := by ennreal_fraction_add
example : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by ennreal_fraction_add
example : (1 : ENNReal) / 18 + (2 / 18 + 0) = 3 / 18 := by ennreal_fraction_add
example : (2 : ENNReal) + 3 = 5 := by ennreal_fraction_add
example : (1 : ENNReal) / 6 + 0 = 1 / 6 := by ennreal_fraction_add
example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by ennreal_fraction_add

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by ennreal_fraction_add

end FractionAddTests

section EdgeCaseTests

-- Test with zero
example : (0 : ENNReal) / 5 = 0 := by ennreal_arith
example : (0 : ENNReal) + 0 = 0 := by ennreal_arith
example : (0 : ENNReal) * 5 = 0 := by ennreal_arith
example : (5 : ENNReal) * 0 = 0 := by ennreal_arith

-- Test with one
example : (1 : ENNReal) * 1 = 1 := by ennreal_arith
example : (5 : ENNReal) / 1 = 5 := by ennreal_arith
example : (1 : ENNReal) / 1 = 1 := by ennreal_arith
example {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by ennreal_arith
example {a : ℕ} : 1 * (↑a : ENNReal) = ↑a := by ennreal_arith

-- Test with infinity (top)
example : (⊤ : ENNReal) + 5 = ⊤ := by simp
example : (5 : ENNReal) + ⊤ = ⊤ := by simp
example : (⊤ : ENNReal) * 5 = ⊤ := by simp [ENNReal.top_mul]

end EdgeCaseTests

section ComplexFractionTests

-- More complex fraction additions
example : (1 : ENNReal) / 2 + 1 / 3 = 5 / 6 := by
  calc (1 : ENNReal) / 2 + 1 / 3
    _ = (3 / 6 : ENNReal) + (1 / 3 : ENNReal) := by
      have : (3 / 6 : ENNReal) = (1 : ENNReal) / 2 := by
        rw [ENNReal.div_eq_div_iff]
        all_goals norm_num
      rw [this]
    _ = (3 / 6 : ENNReal) + (2 / 6 : ENNReal) := by
      have : (1 : ENNReal) / 3 = (2 : ENNReal) / 6 := by
        rw [ENNReal.div_eq_div_iff]
        all_goals norm_num
      rw [this]
    _ = 5 / 6 := by
      rw [ENNReal.div_add_div_same]
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num

example : (1 : ENNReal) / 4 + 1 / 4 = 1 / 2 := by
  ennreal_arith

example : (2 : ENNReal) / 3 + 1 / 6 = 5 / 6 := by
  calc (2 : ENNReal) / 3 + 1 / 6
    _ = (4 / 6 : ENNReal) + (1 / 6 : ENNReal) := by
      have : (4 / 6 : ENNReal) = (2 : ENNReal) / 3 := by
        rw [ENNReal.div_eq_div_iff]
        all_goals norm_num
      rw [this]
    _ = 5 / 6 := by
      rw [ENNReal.div_add_div_same]
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num

example : (3 : ENNReal) / 8 + 1 / 8 = 1 / 2 := by
  ennreal_arith

example : (1 : ENNReal) / 5 + 2 / 5 + 1 / 5 = 4 / 5 := by
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  norm_num

example : (1 : ENNReal) / 2 + 1 / 3 + 1 / 6 = 1 := by
  calc (1 : ENNReal) / 2 + 1 / 3 + 1 / 6
    _ = (3 / 6 : ENNReal) + (1 / 3 : ENNReal) + (1 / 6 : ENNReal) := by
      have : (3 / 6 : ENNReal) = (1 : ENNReal) / 2 := by
        rw [ENNReal.div_eq_div_iff]
        all_goals norm_num
      rw [this]
    _ = (3 / 6 : ENNReal) + (2 / 6 : ENNReal) + (1 / 6 : ENNReal) := by
      have : (1 / 3 : ENNReal) = (2 : ENNReal) / 6 := by
        rw [ENNReal.div_eq_div_iff]
        all_goals norm_num
      rw [this]
    _ = (3 + 2 + 1) / 6 := by
      rw [ENNReal.div_add_div_same]
      exact ENNReal.div_add_div_same
    _ = 6 / 6 := by norm_num
    _ = 1 := by
      rw [ENNReal.div_self]
      all_goals norm_num

example : (1 : ENNReal) / 4 + 1 / 4 + 1 / 2 = 1 := by
   calc (1 : ENNReal) / 4 + 1 / 4 + 1 / 2
     _ = (1 / 4 : ENNReal) + (1 / 4 : ENNReal) + (2 / 4 : ENNReal) := by
       have : (1 / 2 : ENNReal) = (2 : ENNReal) / 4 := by
         rw [ENNReal.div_eq_div_iff]
         all_goals norm_num
       rw [this]
     _ = (1 + 1 + 2) / 4 := by
       rw [ENNReal.div_add_div_same]
       exact ENNReal.div_add_div_same
     _ = 4 / 4 := by norm_num
     _ = 1 := by
       rw [ENNReal.div_self]
       all_goals norm_num

-- Mixed whole numbers and fractions
example : 2 + (1 : ENNReal) / 2 = 5 / 2 := by
  calc 2 + (1 : ENNReal) / 2
    _ = (4 / 2 : ENNReal) + (1 / 2 : ENNReal) := by
      have : (4 / 2 : ENNReal) = (2 : ENNReal) := by
        refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
        all_goals norm_num
        refine div_ne_top ?_ ?_
        all_goals norm_num
      rw [this]
    _ = (4 + 1) / 2 := by
      rw [ENNReal.div_add_div_same]
    _ = 5 / 2 := by norm_num

example : (3 : ENNReal) / 2 + 1 = 5 / 2 := by
  calc (3 : ENNReal) / 2 + 1
    _ = 3 / 2 + 2 / 2 := by
      rw [show (1 : ENNReal) = 2 / 2 by
        rw [ENNReal.div_self]; all_goals norm_num]
    _ = (3 + 2) / 2 := by
      rw [← ENNReal.div_add_div_same]
    _ = 5 / 2 := by norm_num

example : 1 + 2 + (1 : ENNReal) / 2 = 7 / 2 := by
  calc 1 + 2 + (1 : ENNReal) / 2
    _ = (2 : ENNReal) / 2 + 4 / 2 + (1 : ENNReal) / 2 := by
      refine (ENNReal.add_left_inj ?_).mpr ?_
      refine div_ne_top ?_ ?_
      norm_cast
      norm_cast
      rw [ENNReal.div_add_div_same]
      norm_num
      refine (ENNReal.eq_div_iff ?_ ?_).mpr ?_
      all_goals norm_num
    _ = (6 / 2 : ENNReal) + (1 / 2 : ENNReal) := by
      repeat rw [ENNReal.div_add_div_same]
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num
    _ = 7 / 2 := by
      rw [ENNReal.div_add_div_same]
      rw [ENNReal.div_eq_div_iff]
      all_goals norm_num

end ComplexFractionTests

section AlgebraicTests

-- Associativity and commutativity
example {a b c : ℕ} : (↑a + ↑b : ENNReal) + ↑c = ↑a + (↑b + ↑c) := by
  rw [add_assoc]

example {a b : ℕ} : (↑a : ENNReal) + ↑b = ↑b + ↑a := by
  rw [add_comm]

example {a b c : ℕ} : (↑a * ↑b : ENNReal) * ↑c = ↑a * (↑b * ↑c) := by
  rw [mul_assoc]

-- Distributivity
example {a b c : ℕ} : (↑a : ENNReal) * (↑b + ↑c) = ↑a * ↑b + ↑a * ↑c := by
  rw [mul_add]

example {a b c : ℕ} : ((↑a : ENNReal) + ↑b) * ↑c = ↑a * ↑c + ↑b * ↑c := by
  rw [add_mul]

-- Complex algebraic identities
example {a b : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) * ((↑b : ENNReal) / ↑a) = ↑b := by
  rw [ENNReal.mul_div_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

end AlgebraicTests

section InverseTests

-- More inverse transformations
example : (2⁻¹ : ENNReal) = 1 / 2 := by
  ennreal_arith

example : (3⁻¹ : ENNReal) + 6⁻¹ = 1 / 2 := by
  ennreal_arith

example : ((2⁻¹)⁻¹ : ENNReal) = 2 := by
  ennreal_arith

example : (4⁻¹ : ENNReal) * 8 = 2 := by
  rw [← one_div]
  rw [show (8 : ENNReal) = 4 * 2 by ring]
  rw [<- mul_assoc]
  norm_num
  rw[ENNReal.inv_mul_cancel]
  all_goals norm_num


-- Complex inverse patterns
example {a : ℕ} (ha : a ≠ 0) : ((↑a)⁻¹ : ENNReal) * (↑a) = 1 := by
  rw [ENNReal.inv_mul_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

example {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) * (↑a)⁻¹ = 1 := by
  rw [ENNReal.mul_inv_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

end InverseTests

section MixedOperationTests

example : (2 : ENNReal) * 3 / 4 + 1 / 2 = 2 := by
  rw [show (1 : ENNReal) / 2 = 2 / 4 by
    rw [ENNReal.div_eq_div_iff]; all_goals norm_num]
  rw [ENNReal.div_add_div_same]
  refine Eq.symm ((fun {a b} ha hb => (toReal_eq_toReal ha hb).mp) ?_ ?_ ?_)
  norm_cast
  refine div_ne_top ?_ ?_
  all_goals norm_num

example : ((3 : ENNReal) / 4) * (8 / 3) = 2 := by
  calc ((3 : ENNReal) / 4) * (8 / 3)
    _ = (3 * 8) / (4 * 3) := by
      refine Eq.symm (ENNReal.mul_div_mul_comm ?_ ?_)
      all_goals norm_num
    _ = 24 / 12 := by norm_num
    _ = 2 := by
      rw [show (24 : ENNReal) = 2 * 12 by ring]
      rw [mul_div_assoc]
      rw [ENNReal.div_self]
      · simp
      · norm_num
      · norm_num

example : (5 : ENNReal) / 2 - 1 / 2 = 2 := by
  calc (5 : ENNReal) / 2 - 1 / 2
    _ = ((5 - 1) / 2 : ENNReal) := by
      rw [← ENNReal.sub_div]
      intro h1 h2
      norm_num
    _ = 4 / 2 := by
      norm_cast

    _ = 2 := by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num]
      rw [mul_div_assoc]
      rw [ENNReal.div_self]
      · simp
      · norm_num
      · norm_num


example : ((2 : ENNReal) + 3) * 4 / 5 = 4 := by
  calc ((2 : ENNReal) + 3) * 4 / 5
    _ = (5 : ENNReal) * 4 / 5 := by
      norm_num
    _ = 4 := by
      -- rw [mul_div_assoc]
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [ENNReal.div_self]
      all_goals norm_num

example : (6 : ENNReal) / 2 / 3 = 1 := by
  calc (6 : ENNReal) / 2 / 3
    _ = (6 / 2) / 3 := by norm_num
    _ = 6  / (3 * 2) := by

      rw [ENNReal.div_eq_div_iff]
      norm_num
      rw [show (6 : ENNReal) = 3 * 2 by norm_num]
      rw [mul_div_assoc]
      rw [ENNReal.div_self]
      · ring
      · norm_num
      · norm_num
      all_goals norm_num
    _ = 1 := by
      norm_num
      refine (div_eq_one_iff ?_ ?_).mpr rfl
      all_goals norm_num


end MixedOperationTests
