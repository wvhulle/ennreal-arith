
import ENNRealArith

open ENNReal

section BasicSimpTests

example {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by ennreal_basic_simp
example {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by ennreal_basic_simp
example {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by ennreal_basic_simp

example {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by ennreal_basic_simp
example {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by ennreal_basic_simp

example : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_basic_simp
example : (↑2 : ENNReal) * ↑3 = ↑6 := by ennreal_basic_simp

example {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by ennreal_basic_simp
example {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by ennreal_basic_simp

end BasicSimpTests

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
