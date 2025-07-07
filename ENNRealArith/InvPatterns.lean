import ENNRealArith.Common
import ENNRealArith.DivSelf

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/--
Tactic for transforming ENNReal inverse and division expressions.
Handles complex transformations involving inverses, divisions, and multiplications.
Converts between forms like `a⁻¹ * b = b / a` and `(a⁻¹)⁻¹ = a`.
-/
syntax "ennreal_inv_transform" : tactic

elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    -- Try basic reflexivity first
    if ← tryTactic (← `(tactic| rfl)) then return

    -- Try a comprehensive simp with common inverse/division lemmas
    if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                           div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul])) then return

    let tactics : Array (TSyntax `tactic) := #[
      ← `(tactic| rw [inv_inv]),
      ← `(tactic| rw [mul_one]),
      ← `(tactic| rw [one_mul]),
      ← `(tactic| rw [div_eq_mul_inv, one_mul, inv_inv]),
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| (simp only [ mul_one, one_mul, inv_inv, mul_comm, mul_assoc])),
      ← `(tactic| simp only [mul_div, Nat.cast_mul]),
    ]


    -- Try multiplication-inverse equality pattern using sequence
    let mulInvEqInvTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [← div_eq_mul_inv, inv_eq_one_div]),
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence mulInvEqInvTactics then return



    -- Try simpler ofReal pattern
    if ← tryTactic (← `(tactic| simp only [ENNReal.ofReal_div_of_pos] <;> norm_num)) then return

    for tac in tactics do
      if ← tryTactic tac then return



    -- Try division equality pattern using sequence
    let divEqDivTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [ENNReal.div_eq_div_iff]),
      ← `(tactic| all_goals norm_num)
    ]
    if ← tryTacticSequence divEqDivTactics then return


    if ← tryTactic (← `(tactic| (norm_cast; ennreal_div_self))) then return

    -- Try multiplication division cancellation pattern using sequence
    let mulDivCancelTactics : List (TSyntax `tactic) := [
      ← `(tactic| rw [inv_eq_one_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [← mul_div]),
      ← `(tactic| rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)])
    ]
    if ← tryTacticSequence mulDivCancelTactics then return

    -- Try simple inverse-multiplication to division pattern
    if ← tryTacticSequence [← `(tactic| rw [mul_comm, ← div_eq_mul_inv]), ← `(tactic| simp [ne_eq])] then return

    evalTactic (← `(tactic| all_goals assumption))


section TestSuite

-- Core inverse-division transformations
lemma test_inverse_multiplication_to_division {a b : ℕ} (ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform

lemma test_division_as_inverse_multiplication {a b : ℕ} : 
  (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform

-- Double inverse property
lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by ennreal_inv_transform

-- Reciprocal patterns
lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by ennreal_inv_transform

-- Complex pattern example
lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_inv_transform

end TestSuite

end ENNRealArith
