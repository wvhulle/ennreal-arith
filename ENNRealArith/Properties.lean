import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Expr
import Lean.PrettyPrinter
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Lean
import Lean.Util.Trace

open Lean Meta Elab Tactic ENNReal Qq

namespace ENNReal

lemma inv_div_eq_div {a b : ℕ} : (↑a : ENNReal)⁻¹ / (↑b : ENNReal)⁻¹ = ↑b / ↑a := by
   calc
      (↑a : ENNReal)⁻¹ / (↑b : ENNReal)⁻¹
      _ = (↑a : ENNReal)⁻¹ * ((↑b : ENNReal)⁻¹)⁻¹ := by
        rw [div_eq_mul_inv]
      _ = (↑b : ENNReal) * (↑a)⁻¹ := by
        rw [inv_inv]
        rw [mul_comm]
      _ = ↑b / ↑a := by
        rw [<- div_eq_mul_inv]


lemma add_mixed_denom {a b c d : ENNReal} {hc : c ≠ 0} {hd : d ≠ 0} {hct: c ≠ ⊤} {hdt: d ≠ ⊤} :
  a / c + b / d = (a * d + b * c) / (c * d)  := by
    have h1 : a / c = (a * d) / (c * d) := by
      rw [<- ENNReal.mul_div_mul_right] <;> norm_num
      · assumption
      · assumption
    have h2 : b / d = (b * c) / (c * d) := by
      rw [mul_comm c d]
      rw [<- ENNReal.mul_div_mul_right] <;> norm_num
      · assumption
      · assumption
    rw [h1, h2]
    rw [← ENNReal.div_add_div_same]


lemma div_div_cast {a b c : ℕ}:
  ((↑a : ENNReal) / ↑b) / ↑c = ↑a / (↑b * ↑c) := by
  calc ((↑a : ENNReal) / ↑b) / ↑c
    _ = (↑a : ENNReal) / ↑b * (↑c)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (↑a : ENNReal) * (↑b)⁻¹ * (↑c)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (↑a : ENNReal) * ((↑b)⁻¹ * (↑c)⁻¹) := by
      rw [mul_assoc]
    _ = (↑a : ENNReal) * ((↑b * ↑c)⁻¹) := by
      congr 1
      rw [ENNReal.mul_inv]
      all_goals norm_num
    _ = (↑a : ENNReal) / (↑b * ↑c) := by
      rw [← div_eq_mul_inv]




lemma div_div {a b c : ENNReal} {h: b ≠ 0} {g: c ≠ 0}:
  (a / b) / c = a / (b * c) := by
  calc (a / b) / c
    _ = (a / b) * c⁻¹ := by
      rw [div_eq_mul_inv]
    _ = a * b⁻¹ * c⁻¹ := by
      rw [div_eq_mul_inv]
    _ = a  * ((b)⁻¹ * (c)⁻¹) := by
      rw [mul_assoc]
    _ = a * ((b * c)⁻¹) := by
      congr 1
      rw [ENNReal.mul_inv]
      . exact Or.inl h
      . exact Or.inr g
    _ = a   / (b * c) := by
      rw [← div_eq_mul_inv]


lemma add_div_eq_div {a b c  : ENNReal} {hc : c ≠ 0}  {hct: c ≠ ⊤}  :
  a + b / c = (a * c + b ) / c  := by
    have h1 : a = (a * c) / c := by
      exact Eq.symm (ENNReal.mul_div_cancel_right hc hct)
    rw [h1]

    rw [ENNReal.div_add_div_same]
    rw [ENNReal.div_eq_div_iff]
    rw [mul_div_assoc]
    rw [ENNReal.div_self]
    ring
    all_goals assumption


lemma div_eq_iff {a b c : ENNReal} {hc : c ≠ 0} {hct: c ≠ ⊤} :
  a / c = b ↔ a = b * c := by
    constructor
    · intro h
      rw [<- ENNReal.mul_right_inj hc] at h
      have: c * ( a / c ) = c * a / c := by
        exact Eq.symm (mul_div_assoc c a c)
      rw [this] at h
      rw [mul_comm] at h
      rw [ENNReal.mul_div_cancel_right hc hct] at h
      rw [mul_comm] at h
      exact h
      assumption
    · intro h
      rw [h]
      rw [ENNReal.mul_div_cancel_right hc hct]
