import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_mul_div_assoc" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do

    let tryTactic (tac : TacticM Unit) : TacticM Bool := do
      try tac; return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    let tryNonzeroProof : TacticM Unit := do
      try evalTactic (← `(tactic| assumption)); return
      catch _ => try evalTactic (← `(tactic| apply ne_of_gt)); evalTactic (← `(tactic| assumption)); return
      catch _ => try evalTactic (← `(tactic| norm_num)); return
      catch _ => try evalTactic (← `(tactic| exact Nat.succ_ne_zero _)); return
      catch _ => throwError "Could not prove nonzero condition"

    let tryRewrite (rw : TSyntax `tactic) (withNorm : Bool := false) : TacticM Bool :=
      tryTactic do
        evalTactic rw
        if withNorm then evalTactic (← `(tactic| norm_cast))

    if ← tryTactic do
      evalTactic (← `(tactic| rw [ENNReal.div_mul_cancel]))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      tryNonzeroProof
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    then return


    let patterns := [
      (← `(tactic| rw [mul_div]), ← `(tactic| rw [← mul_div])),
      (← `(tactic| rw [ENNReal.mul_comm_div, mul_div]), ← `(tactic| rw [← ENNReal.mul_comm_div, ← mul_div])),
      (← `(tactic| rw [div_mul_eq_mul_div]), ← `(tactic| rw [← div_mul_eq_mul_div])),
      (← `(tactic| rw [mul_div, mul_assoc]), ← `(tactic| rw [← mul_div, ← mul_assoc]))
    ]


    for (fwd, bwd) in patterns do
      if ← tryRewrite fwd then return
      if ← tryRewrite bwd then return

    let basicPatterns := patterns.take 2
    for (fwd, bwd) in basicPatterns do
      if ← tryRewrite fwd true then return
      if ← tryRewrite bwd true then return

    if ← tryRewrite (← `(tactic| simp only [mul_div, mul_assoc, one_mul, mul_one])) then return

    throwError "ennreal_mul_div_assoc could not solve the goal"


section TestSuite


lemma ennreal_mul_div_assoc_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_assoc_basic {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_assoc_reverse_manual {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  rw [← mul_div]

lemma ennreal_mul_div_assoc_reverse {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_two_three_five_manual : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_two_three_five : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_mul_div_four_seven_manual : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  rw [mul_div]

lemma ennreal_mul_div_four_seven : (↑4 : ENNReal) * ((↑1 : ENNReal) / (↑7 : ENNReal)) = (↑4 * ↑1 : ENNReal) / (↑7 : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_cast_manual {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  rw [mul_div]
  norm_cast

lemma ennreal_mul_div_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_chain_manual {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  rw [mul_div, mul_assoc]

lemma ennreal_mul_div_chain {a b c d : ℕ} : ((↑a : ENNReal) * (↑b : ENNReal)) * ((↑c : ENNReal) / (↑d : ENNReal)) = (↑a * ↑b * ↑c : ENNReal) / (↑d : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_mul_div_one_manual {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  rw [mul_div]

lemma ennreal_mul_div_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / 1) = (↑a * ↑b : ENNReal) / 1 := by
  ennreal_mul_div_assoc

lemma ennreal_one_mul_div_manual {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  rw [mul_div]

lemma ennreal_one_mul_div {b c : ℕ} : (1 : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (1 * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc


lemma ennreal_div_mul_cancel_manual {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  rw [ENNReal.div_mul_cancel]
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)
  · exact ENNReal.coe_ne_top

lemma ennreal_div_mul_cancel {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  ennreal_mul_div_assoc


lemma ennreal_div_mul_right_manual {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  rw [ENNReal.mul_comm_div]
  rw [mul_div]

lemma ennreal_div_mul_right {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

lemma ennreal_div_mul_concrete : ((↑6 : ENNReal) / (↑2 : ENNReal)) * (↑3 : ENNReal) = (↑6 * ↑3 : ENNReal) / (↑2 : ENNReal) := by
  ennreal_mul_div_assoc

end TestSuite

end ENNRealArith
