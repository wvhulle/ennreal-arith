import ENNRealArith

open ENNReal

example: ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by ennreal_arith

example : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith
example : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith
example {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

example : (18 : ENNReal) / 18 = 1 := by ennreal_arith
example : @Eq ENNReal (18 / 18) 1 := by ennreal_arith
example : @HDiv.hDiv ENNReal ENNReal ENNReal instHDiv 18 18 = @OfNat.ofNat ENNReal 1 One.toOfNat1 := by ennreal_arith
example {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_arith
example {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by ennreal_arith

example : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith
example : (0 : ENNReal) + 5 * 0 + 0 / 3 = 0 := by ennreal_arith
example {a : ℕ} : (↑a : ENNReal) * 1 / 1 * 1 = ↑a := by ennreal_arith
example: (2 : ENNReal) + 3 = 5 := by ennreal_arith

example : ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by ennreal_arith
example : (18 : ENNReal) / 18 = 1 := by ennreal_arith
example : ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by ennreal_fraction_add
example : (18 : ENNReal) / 18 = 1 := by apply ENNReal.div_self <;> norm_num
example : ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by ennreal_arith
example : ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by first | ennreal_arith

example {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by ennreal_arith

example (p q : Prop) [Decidable p] [Decidable q] :
  (if p then (0 : ENNReal) else if q then 1/18 else
    ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18) =
  (if p then 0 else if q then 1/18 else 1) := by
  split_ifs <;> ennreal_arith
