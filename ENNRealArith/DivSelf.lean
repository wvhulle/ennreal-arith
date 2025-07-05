import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

syntax "ennreal_div_self" : tactic

elab_rules : tactic | `(tactic| ennreal_div_self) => do
  let goal ← getMainGoal
  goal.withContext do
    let tryNonzeroProof : TacticM Unit := do
      try
        evalTactic (← `(tactic| assumption))
      catch _ =>
        try
          evalTactic (← `(tactic| apply ne_of_gt; assumption))
        catch _ =>
          try
            evalTactic (← `(tactic| norm_num))
          catch _ =>
            try
              evalTactic (← `(tactic| exact Nat.succ_ne_zero _))
            catch _ =>
              throwError "Could not prove nonzero condition"

    try
      evalTactic (← `(tactic| apply ENNReal.div_self))
      evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
      evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
      tryNonzeroProof
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    throwError "ennreal_div_self could not solve the goal"



section TestSuite

lemma ennreal_div_same_manual_ne_zero {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr ha)) ENNReal.coe_ne_top

lemma ennreal_div_same_ne_zero {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_div_self

lemma ennreal_div_same_manual_pos {a : ℕ} (ha : 0 < a) : (↑a : ENNReal) / ↑a = 1 := by
  exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt ha))) ENNReal.coe_ne_top

lemma ennreal_div_same_pos {a : ℕ} (ha : 0 < a) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_div_self

lemma ennreal_div_two_two_manual : (↑2 : ENNReal) / ↑2 = 1 := by
  exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_two_two : (↑2 : ENNReal) / ↑2 = 1 := by
  ennreal_div_self

lemma ennreal_div_three_three_manual : (↑3 : ENNReal) / ↑3 = 1 := by
  exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by norm_num))) ENNReal.coe_ne_top

lemma ennreal_div_three_three : (↑3 : ENNReal) / ↑3 = 1 := by
  ennreal_div_self

lemma ennreal_div_succ_succ_manual {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by
  exact ENNReal.div_self (ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) ENNReal.coe_ne_top

lemma ennreal_div_succ_succ {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by
  ennreal_div_self



end TestSuite

end ENNRealArith
