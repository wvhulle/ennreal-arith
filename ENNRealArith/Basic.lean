import ENNRealArith.ArithmeticCore
import ENNRealArith.FractionOperations
-- import Qq
open Lean Meta Elab Tactic ENNReal Qq
namespace ENNRealArith



-- =============================================
-- DIVISION BY SELF TACTIC
-- =============================================

/--
Tactic for proving ENNReal division by self equals 1.
Handles goals of the form `(↑a : ENNReal) / ↑a = 1` where `a : ℕ`.
-/
syntax "ennreal_div_self" : tactic

elab_rules : tactic | `(tactic| ennreal_div_self) =>  do

  -- Try special handling for division patterns using Qq
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget
    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q($a / $b = (1 : ENNReal)) =>
      -- Check if a and b are the same expression
      if a == b then
        evalTactic (← `(tactic| rw [ENNReal.div_eq_one_iff] <;> norm_num))
        try
          tryNonzeroProof
        catch _ => pure ()
        if (← getUnsolvedGoals).isEmpty then return
    | _ => pure ()
  -- First try norm_num for concrete numeric cases
  if ← tryTactic (← `(tactic| norm_num)) then return



  -- Try simp with ENNReal.div_self lemma directly
  if ← tryTactic (← `(tactic| simp only [ENNReal.div_self, ENNReal.coe_ne_zero, ENNReal.coe_ne_top, Nat.cast_ne_zero])) then
    -- If simp made progress, try to finish with assumption or norm_num
    let _ ← tryTactic (← `(tactic| assumption))
    let _ ← tryTactic (← `(tactic| norm_num))
    if (← getUnsolvedGoals).isEmpty then return

  -- Try using div_eq_one_iff
  try
    evalTactic (← `(tactic| rw [div_eq_one_iff]))
    evalTactic (← `(tactic| all_goals norm_num))
    tryNonzeroProof
    if (← getUnsolvedGoals).isEmpty then return
  catch _ => pure ()

  -- Original approach for general case
  try
    evalTactic (← `(tactic| apply ENNReal.div_self))
    -- First goal: prove a ≠ 0
    evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
    evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
    tryNonzeroProof
    -- Second goal: prove a ≠ ⊤
    evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    if (← getUnsolvedGoals).isEmpty then return
  catch _ => pure ()

  throwError "ennreal_div_self could not solve the goal"


-- =============================================
-- BASIC SIMPLIFICATION TACTIC
-- =============================================

/--
Tactic for basic ENNReal simplifications using norm_num, norm_cast, and simp.
Tries various combinations of these tactics to solve simple arithmetic goals.
-/
syntax "ennreal_basic_simp" : tactic

elab_rules : tactic | `(tactic| ennreal_basic_simp) => do
  if ← tryBasicComputation then return

  if ← tryTactic (← `(tactic| simp)) then return

  let tacticSequences := [
    [← `(tactic| norm_cast), ← `(tactic| norm_num)],
    [<- `(tactic | (
        apply div_ne_top
        all_goals norm_num
    ))],
    [← `(tactic| simp only [add_zero, zero_add, inv_eq_one_div])],
    [← `(tactic| simp only [add_zero, zero_add]), ← `(tactic| norm_num)],
    [<- `(tactic| (
        rw [<- toReal_eq_toReal_iff']
        · norm_num
        · exact div_ne_top (by norm_num) (by norm_num)
        all_goals norm_num

    ))],

    [← `(tactic| rw [ENNReal.div_eq_div_iff]), ← `(tactic| all_goals norm_num)],



  ]

  for sequence in tacticSequences do
    if ← tryTacticSequence sequence then return

  try
    evalTactic (← `(tactic| (
      apply div_ne_top
      all_goals norm_num
      repeat rw [inv_eq_one_div]
    )))
  catch _ => pure ()

example: ¬((3: ENNReal) / 18 = ⊤) := by
  ennreal_basic_simp




example: 30 / 6 = (5 : ENNReal) :=by
        rw [<- toReal_eq_toReal_iff']
        · norm_num
        · exact div_ne_top (by norm_num) (by norm_num)
        all_goals norm_num

-- =============================================
-- MULTIPLICATION CANCELLATION TACTIC
-- =============================================

/--
Tactic for canceling common factors in ENNReal multiplication/division expressions.
Handles patterns like `(↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b)`.
-/
syntax "ennreal_mul_cancel" : tactic

elab_rules : tactic | `(tactic| ennreal_mul_cancel) => do
  let goal ← getMainGoal
  goal.withContext do
    try
      evalTactic (← `(tactic| simp only [Nat.cast_mul, zero_mul, mul_one, one_mul, mul_zero,
                                        ENNReal.zero_div, Nat.cast_zero, Nat.cast_one]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    let attemptCancellation : TacticM Bool := do
      try
        evalTactic (← `(tactic| rw [Nat.cast_mul, Nat.cast_mul]))
      catch _ => pure ()

      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_right))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => pure ()

      try
        evalTactic (← `(tactic| apply ENNReal.mul_div_mul_left))
        evalTactic (← `(tactic| apply ENNReal.coe_ne_zero.mpr))
        evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
        tryNonzeroProof
        evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
        return (← getUnsolvedGoals).isEmpty
      catch _ => return false

    if ← attemptCancellation then return

    -- Try with commutativity rewriting
    let attemptWithComm : TacticM Bool := do
      try
        -- Try rewriting mul_comm in numerator and denominator
        evalTactic (← `(tactic| conv_lhs => arg 1; rw [mul_comm]))
        if ← attemptCancellation then return true
        else return false
      catch _ =>
        try
          evalTactic (← `(tactic| conv_lhs => arg 2; rw [mul_comm]))
          if ← attemptCancellation then return true
          else return false
        catch _ =>
          try
            evalTactic (← `(tactic| conv_lhs => arg 1; rw [mul_comm]; arg 2; rw [mul_comm]))
            if ← attemptCancellation then return true
            else return false
          catch _ => return false

    if ← attemptWithComm then return

    try
      evalTactic (<- `(tactic |
          (
            rw [mul_div_assoc]
            try rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

          )
      ))
    catch _ => pure ()

    try
      evalTactic (<- `(tactic |
          (
            rw [ENNReal.div_self (by norm_num) (by norm_num)]
            all_goals norm_num

          )
      ))
    catch _ => pure ()
-- =============================================
-- TEST SUITES
-- =============================================

section BasicSimpTests

-- Essential identity tests
lemma test_addition_right_identity {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by ennreal_basic_simp
lemma test_addition_left_identity {a : ℕ} : 0 + (↑a : ENNReal) = ↑a := by ennreal_basic_simp
lemma test_multiplication_right_identity {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by ennreal_basic_simp
lemma test_multiplication_left_identity {a : ℕ} : 1 * (↑a : ENNReal) = ↑a := by ennreal_basic_simp
lemma test_division_by_one {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by ennreal_basic_simp

-- Key absorption properties
lemma test_multiplication_zero_absorbing_right {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by ennreal_basic_simp
lemma test_multiplication_zero_absorbing_left {a : ℕ} : 0 * (↑a : ENNReal) = 0 := by ennreal_basic_simp
lemma test_zero_divided_by_any {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by ennreal_basic_simp

-- Core concrete examples
lemma test_addition_concrete : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_basic_simp
lemma test_multiplication_concrete : (↑2 : ENNReal) * ↑3 = ↑6 := by ennreal_basic_simp
lemma test_larger_addition : (↑10 : ENNReal) + ↑15 = ↑25 := by ennreal_basic_simp
lemma test_larger_multiplication : (↑7 : ENNReal) * ↑8 = ↑56 := by ennreal_basic_simp

-- Cast preservation (essential for interoperability)
lemma test_addition_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ) := by ennreal_basic_simp
lemma test_multiplication_preserves_nat_cast {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by ennreal_basic_simp

-- Multiple operations
lemma test_multiple_additions : (↑1 : ENNReal) + ↑2 + ↑3 = ↑6 := by ennreal_basic_simp
lemma test_multiple_multiplications : (↑2 : ENNReal) * ↑3 * ↑4 = ↑24 := by ennreal_basic_simp
lemma test_mixed_identities {a : ℕ} : (↑a : ENNReal) + 0 + 0 = ↑a := by ennreal_basic_simp
lemma test_zero_patterns : (↑0 : ENNReal) + 0 = 0 := by ennreal_basic_simp

-- inv_eq_one_div rewriting
lemma test_inverse_as_division {a : ℕ} : (↑a : ENNReal)⁻¹ = 1 / ↑a := by ennreal_basic_simp

end BasicSimpTests

section DivSelfTests

-- Core division by self functionality
lemma test_division_self_nonzero {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_div_self

lemma test_division_self_nonzero_manual {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  apply ENNReal.div_self
  · exact ENNReal.coe_ne_zero.mpr (Nat.cast_ne_zero.mpr (by assumption))
  · exact ENNReal.coe_ne_top

lemma test_division_self_successor {n : ℕ} : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by
  ennreal_div_self

-- Concrete examples
lemma test_division_self_concrete : (↑2 : ENNReal) / ↑2 = 1 := by ennreal_div_self
lemma test_division_self_concrete_5 : (↑5 : ENNReal) / ↑5 = 1 := by ennreal_div_self
lemma test_division_self_concrete_100 : (↑100 : ENNReal) / ↑100 = 1 := by ennreal_div_self

-- Different numeric literal forms
lemma test_division_self_ofNat : (7 : ENNReal) / 7 = 1 := by ennreal_div_self

-- Successor patterns
lemma test_division_self_succ_zero : (↑(0 + 1) : ENNReal) / ↑(0 + 1) = 1 := by

  ennreal_div_self


lemma test_division_self_succ_pattern {n : ℕ} : (↑(Nat.succ n) : ENNReal) / ↑(Nat.succ n) = 1 := by ennreal_div_self

end DivSelfTests

section MulCancelTests

example : 6 * 5 / 6 = (5 : ENNReal) := by
  rw [mul_div_assoc]
  rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

-- Core cancellation functionality
lemma test_division_cancellation_right {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by ennreal_mul_cancel
lemma test_division_cancellation_left {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(c * b)) = (↑a) / (↑b) := by ennreal_mul_cancel

-- Concrete examples
lemma test_division_cancellation_concrete : (↑(3 * 2) : ENNReal) / (↑(5 * 2)) = (↑3) / (↑5) := by
  have : (2 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

lemma test_division_cancellation_larger : (↑(7 * 11) : ENNReal) / (↑(13 * 11)) = (↑7) / (↑13) := by
  have : (11 : ℕ) ≠ 0 := by norm_num
  ennreal_mul_cancel

-- Special cases
lemma test_division_cancellation_zero_numerator {b c : ℕ} : (↑(0 * c) : ENNReal) / (↑(b * c)) = (↑0) / (↑b) := by ennreal_mul_cancel
lemma test_division_cancellation_same_numerator_denominator {c : ℕ} (hc : c ≠ 0) : (↑(5 * c) : ENNReal) / (↑(5 * c)) = (↑5) / (↑5) := by ennreal_mul_cancel

-- Identity cancellation
lemma test_division_cancellation_one_left {a b : ℕ} : (↑(1 * a) : ENNReal) / (↑(1 * b)) = (↑a) / (↑b) := by ennreal_mul_cancel
lemma test_division_cancellation_one_right {a b : ℕ} : (↑(a * 1) : ENNReal) / (↑(b * 1)) = (↑a) / (↑b) := by ennreal_mul_cancel

-- Multiple factor patterns
lemma test_division_cancellation_commuted {a b c : ℕ} (hc : c ≠ 0) : (↑(c * a) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_mul_cancel

end MulCancelTests



/-!
# ENNReal Fraction Operations

This module contains tactics for advanced fraction and inverse operations:
- Multiplication/division associativity (`ennreal_mul_div_assoc`)
- Inverse pattern transformations (`ennreal_inv_transform`)
- Fraction addition and simplification (`ennreal_fraction_add`)

These handle more complex ENNReal expressions involving fractions, inverses, and mixed operations.
-/

-- =============================================
-- MULTIPLICATION/DIVISION ASSOCIATIVITY TACTIC
-- =============================================

syntax "ennreal_mul_div_assoc" : tactic

/--
Tactic for proving ENNReal multiplication-division associativity.
Handles goals of the form `(↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal)`.
-/
elab_rules : tactic | `(tactic| ennreal_mul_div_assoc) => do
  let goal ← getMainGoal
  goal.withContext do

    try
      evalTactic (← `(tactic| simp only [mul_div, ENNReal.mul_comm_div,  one_mul, mul_one, Nat.cast_mul]))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    evalTactic (← `(tactic| apply ENNReal.div_self))
    evalTactic (← `(tactic| apply Nat.cast_ne_zero.mpr))
    evalTactic (← `(tactic| assumption))
    evalTactic (← `(tactic| exact ENNReal.coe_ne_top))

    if (← getUnsolvedGoals).isEmpty then return

    try
      evalTactic (<- `(tactic|
        rw [ENNReal.div_self (by norm_num) (by norm_num)]
      ))
    catch _ => pure ()

    try
      evalTactic (<- `(tactic |
          (
            rw [mul_div_assoc]
            rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
            all_goals norm_num
          )
      ))
    catch _ => pure ()

-- =============================================
-- INVERSE PATTERN TRANSFORMATION TACTIC
-- =============================================

syntax "ennreal_inv_transform" : tactic

/--
Tactic for transforming ENNReal inverse and division expressions.
Handles complex transformations involving inverses, divisions, and multiplications.
Converts between forms like `a⁻¹ * b = b / a` and `(a⁻¹)⁻¹ = a`.
-/
elab_rules : tactic | `(tactic| ennreal_inv_transform) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget
    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q(1⁻¹ = (1 : ENNReal)) =>
      evalTactic (← `(tactic| rw [inv_one]))
      pure ()
    | ~q((↑$a : ENNReal) * (↑$a : ENNReal)⁻¹ = (1 : ENNReal)) =>
      -- For natural number coercions, handle the conditions properly
      evalTactic (← `(tactic| rw [ENNReal.mul_inv_cancel]))
      -- First goal (h0): prove ↑a ≠ 0
      evalTactic (← `(tactic| focus
        apply ENNReal.coe_ne_zero.mpr
        apply Nat.cast_ne_zero.mpr
        assumption))
      -- Second goal (ht): prove ↑a ≠ ⊤
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    | ~q($a * $a⁻¹ = (1 : ENNReal) ) =>
      -- Check if a and b are the same expression
      evalTactic (<- `(tactic | rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]))
    | ~q((↑$a : ENNReal)⁻¹ * (↑$a : ENNReal) = (1 : ENNReal)) =>
      -- Handle inv_mul_cancel for natural number coercions
      evalTactic (← `(tactic| rw [ENNReal.inv_mul_cancel]))
      -- First goal (h0): prove ↑a ≠ 0
      evalTactic (← `(tactic| focus
        apply ENNReal.coe_ne_zero.mpr
        apply Nat.cast_ne_zero.mpr
        assumption))
      -- Second goal (ht): prove ↑a ≠ ⊤
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
    | ~q($a⁻¹ * $a = (1 : ENNReal)) =>
      -- Handle general inv_mul_cancel
      evalTactic (<- `(tactic | rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]))
    | _ => pure ()
    -- Try basic reflexivity first



    if ← tryTactic (← `(tactic| rfl)) then return
    -- Try a comprehensive simp with common inverse/division lemmas
    if ← tryTactic (← `(tactic| simp only [mul_one, one_mul, inv_inv, mul_comm, mul_assoc,
                                           div_eq_mul_inv, inv_eq_one_div, mul_div, Nat.cast_mul, mul_inv])) then return

    -- Try specific pattern for (a⁻¹ * b⁻¹)⁻¹ = a * b
    if ← tryTacticSequence [
      ← `(tactic| rw [ENNReal.mul_inv]),
      ← `(tactic| repeat rw [inv_inv]),
      ← `(tactic| all_goals norm_num)
    ] then return

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

    -- Try basic division by self pattern
    if ← tryTactic (← `(tactic| simp only [ENNReal.div_self] <;> norm_num)) then return

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



    -- Try to apply mul_inv_cancel manually
    try
      evalTactic (← `(tactic| apply ENNReal.mul_inv_cancel))
      -- First goal: prove a ≠ 0
      evalTactic (← `(tactic| assumption))
      -- Second goal: prove a ≠ ⊤
      evalTactic (← `(tactic| exact ENNReal.coe_ne_top))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()

    try
      evalTactic (← `(tactic| all_goals assumption))
    catch _ => pure ()

-- =============================================
-- FRACTION ADDITION TACTIC
-- =============================================

/-- Convert an ENNReal equation to a Real equation when both sides are not infinity -/
lemma ennreal_eq_via_toReal {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a = b ↔ a.toReal = b.toReal := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, h]


-- General lemma for adding fractions with different denominators
lemma ennreal_fraction_add_general {a b c d : ENNReal} {hc : c ≠ 0} {hd : d ≠ 0} {hct: c ≠ ⊤} {hdt: d ≠ ⊤} :
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

    -- General lemma for adding fractions with different denominators
lemma ennreal_add_div {a b c  : ENNReal} {hc : c ≠ 0}  {hct: c ≠ ⊤}  :
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

syntax "ennreal_fraction_add" : tactic

/-- Simplify expressions of ENNReals that contain additions and fractions. -/
elab_rules : tactic | `(tactic| ennreal_fraction_add) => do
  let _ ← tryTactic (← `(tactic| simp only [add_zero, zero_add]))

  if (← getUnsolvedGoals).isEmpty then return

  let goal ← getMainGoal
  goal.withContext do
    let target ← getMainTarget
    have targetQ : Q(Prop) := target
    match targetQ with
    | ~q( (_ : ENNReal ) / $c + _ / $d + _ = _) =>
      -- Check if a and b are the same expression
      evalTactic (← `(tactic| (repeat
                                repeat rw [inv_eq_one_div]
                                rw [ennreal_fraction_add_general] <;> norm_num
                                repeat rw [inv_eq_one_div]
                               ennreal_inv_transform)))
      if (← getUnsolvedGoals).isEmpty then return
    | ~q( $a / $c + $b / $d = ($e : ENNReal)) =>
      -- Check if a and b are the same expression
      evalTactic (← `(tactic| rw [ennreal_fraction_add_general] <;> all_goals norm_num))
      if (← getUnsolvedGoals).isEmpty then return
    | ~q( $a + $b / $c = ($e : ENNReal)) =>
      -- Check if a and b are the same expression
      evalTactic (← `(tactic| rw [ennreal_add_div] <;> all_goals norm_num))
      if (← getUnsolvedGoals).isEmpty then return
    | ~q( $a / $b + $c = ($e : ENNReal)) =>
      -- Check if a and b are the same expression
      evalTactic (← `(tactic| (rw [add_comm]; rw [ennreal_add_div] <;> all_goals norm_num)))
      if (← getUnsolvedGoals).isEmpty then return
    | _ => pure ()



  try
    evalTactic (← `(tactic| (
      repeat
        repeat rw [inv_eq_one_div]
        rw [ennreal_fraction_add_general] <;> norm_num
        repeat rw [inv_eq_one_div]
      ennreal_inv_transform)))
    if (← getUnsolvedGoals).isEmpty then return
  catch _ => pure ()


  -- Try norm_num for simple arithmetic
  if ← tryTactic (← `(tactic| norm_num)) then return

  -- Convert inverses to divisions and simplify nested additions
  let _ ← tryTactic (← `(tactic| simp only [add_assoc, add_zero, zero_add, inv_eq_one_div]))
  if (← getUnsolvedGoals).isEmpty then return

  -- Handle multiple fractions with same denominator by associating and combining
  -- This will repeatedly combine fractions from left to right
  let _ ← tryTactic (← `(tactic| repeat (first | rw [← ENNReal.div_add_div_same] | rw [add_assoc])))
  if (← getUnsolvedGoals).isEmpty then return

  -- Repeatedly combine additions with division
  repeatWhileProgress (← `(tactic| rw [← ENNReal.add_div]))

  -- Try inverse transformations
  let _ ← tryTactic (← `(tactic| ennreal_inv_transform))


  -- Try division by self for cases like 18/18 = 1
  if ← tryTactic (← `(tactic| ennreal_div_self)) then return

  -- If still not solved, try the toReal approach
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| rw [ENNRealArith.ennreal_eq_via_toReal (by norm_num) (by norm_num)]),
      ← `(tactic| rw [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]),
      ← `(tactic| all_goals norm_num),
    ]

  -- Try different denominator handling by converting to common denominator
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| rw [div_add_div_same]),
      ← `(tactic| norm_num),
    ]

  -- Try with field_simp for rational arithmetic
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTactic (← `(tactic| field_simp))
    -- let _ ← tryTactic (← `(tactic| norm_num))

  -- Final attempt with more aggressive rewriting
  if !(← getUnsolvedGoals).isEmpty then
    let _ ← tryTacticSequence [
      ← `(tactic| simp only [inv_eq_one_div]),
      ← `(tactic| rw [← ENNReal.add_div]),
      ← `(tactic| norm_num),
    ]

  try
    evalTactic (← `(tactic| ennreal_basic_simp))
  catch _ => pure ()

lemma test_complex_nested : ((1 : ENNReal) / 2 + 1 / 3) / 5 = 1 / 6 := by
  --
  ennreal_fraction_add



-- =============================================
-- TEST SUITES
-- =============================================

section MulDivAssocTests




-- Multiplication-division associativity lemmas
lemma examples  : (6: ENNReal) * 5 / 6 = 5 := by
  ennreal_mul_cancel


-- Chained divisions
lemma test_chained_divisions {a b c : ℕ}:
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



-- Multiplication-division associativity lemmas
lemma test_mul_div_associativity_right {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_left {a b c : ℕ} : (↑a * ↑b : ENNReal) / (↑c : ENNReal) = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by
  ennreal_mul_div_assoc

-- Concrete associativity examples
lemma test_mul_div_associativity_concrete : (↑2 : ENNReal) * ((↑3 : ENNReal) / (↑5 : ENNReal)) = (↑2 * ↑3 : ENNReal) / (↑5 : ENNReal) := by
  ennreal_mul_div_assoc

lemma test_mul_div_associativity_larger : (↑10 : ENNReal) * ((↑15 : ENNReal) / (↑25 : ENNReal)) = (↑10 * ↑15 : ENNReal) / (↑25 : ENNReal) := by
  ennreal_mul_div_assoc

-- Cast preservation
lemma test_mul_div_associativity_preserves_cast {a b c : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = ↑(a * b) / (↑c : ENNReal) := by
  ennreal_mul_div_assoc

-- Division-multiplication associativity
lemma test_div_mul_associativity {a b c : ℕ} : ((↑a : ENNReal) / (↑b : ENNReal)) * (↑c : ENNReal) = (↑a * ↑c : ENNReal) / (↑b : ENNReal) := by
  ennreal_mul_div_assoc

-- Chain patterns
lemma test_mul_div_chain {a b c d : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) * (↑d : ENNReal) = (↑(a * b * d) : ENNReal) / (↑c : ENNReal) := by
  -- This requires more complex associativity handling
  ennreal_mul_div_assoc

-- Identity patterns
lemma test_mul_div_one {a b : ℕ} : (↑a : ENNReal) * ((↑b : ENNReal) / (↑1 : ENNReal)) = (↑a * ↑b : ENNReal) / (↑1 : ENNReal) := by
  ennreal_mul_div_assoc

end MulDivAssocTests

section InvPatternTests

-- Core inverse-division transformations
lemma test_inverse_multiplication_to_division {a b : ℕ} (ha : a ≠ 0) :
  (↑a : ENNReal)⁻¹ * (↑b : ENNReal) = (↑b : ENNReal) / (↑a : ENNReal) := by ennreal_inv_transform

lemma test_division_as_inverse_multiplication {a b : ℕ} :
  (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) * (↑b : ENNReal)⁻¹ := by ennreal_inv_transform

-- Double inverse property
lemma test_double_inverse_identity {a : ℕ} : ((↑a : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) := by ennreal_inv_transform

-- Triple inverse
lemma test_triple_inverse {a : ℕ} : (((↑a : ENNReal)⁻¹)⁻¹)⁻¹ = (↑a : ENNReal)⁻¹ := by ennreal_inv_transform

-- Reciprocal patterns
lemma test_reciprocal_as_inverse {a : ℕ} : (1 : ENNReal) / (↑a : ENNReal) = (↑a : ENNReal)⁻¹ := by ennreal_inv_transform

-- Complex pattern example
lemma test_inverse_fraction_multiplication {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑a * ↑b : ENNReal) / (↑c : ENNReal) := by ennreal_inv_transform

-- Inverse of one
lemma test_one_inverse : (1 : ENNReal)⁻¹ = 1 := by
  ennreal_inv_transform

-- Multiplication by inverse patterns
lemma test_mul_inv_cancel_left {a : ℕ}  {h: a ≠ 0}: (↑a : ENNReal) * (↑a : ENNReal)⁻¹ = 1 := by
  ennreal_inv_transform

lemma test_mul_inv_cancel_right {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal)⁻¹ * (↑a : ENNReal) = 1 := by
  ennreal_inv_transform

-- Complex inverse expressions
lemma test_complex_inverse_pattern {a b : ℕ} : ((↑a : ENNReal)⁻¹ * (↑b : ENNReal)⁻¹)⁻¹ = (↑a : ENNReal) * (↑b : ENNReal) := by
  ennreal_inv_transform

end InvPatternTests

section FractionAddTests

lemma test_nested_addition_division :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_fraction_add

lemma test_addition_then_division : ((1 : ENNReal) + 2) / 18 = 3 / 18 := by
  ennreal_fraction_add

lemma test_fraction_addition_same_denominator : (1 : ENNReal) / 18 + 2 / 18 = 3 / 18 := by
  ennreal_fraction_add



lemma test_fraction_addition_different_denominators : (1 : ENNReal) / 2 + 1 / 3 = 5 / 6 := by
  ennreal_fraction_add

lemma test_fraction_addition_with_zero : (1 : ENNReal) / 18 + (2 / 18 + 0) = 3 / 18 := by
  ennreal_fraction_add

lemma test_basic_arithmetic : (2 : ENNReal) + 3 = 5 := by
  ennreal_fraction_add

lemma test_zero_addition : (1 : ENNReal) / 6 + 0 = 1 / 6 := by
  ennreal_fraction_add

-- Multiple fraction additions
lemma test_three_fractions : (1 : ENNReal) / 6 + 1 / 6 + 1 / 6 = 1 / 2 := by
  ennreal_fraction_add


lemma test_mixed_whole_fraction : (2 : ENNReal) + 1 / 2 = 5 / 2 := by
  ennreal_fraction_add

lemma test_complex_expression_2 : (↑10 : ENNReal) / ↑2 + ↑3 * ↑2 = ↑11 := by
  ennreal_fraction_add


example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by
  ennreal_fraction_add

-- Associativity of fraction addition
lemma test_fraction_add_assoc : ((1 : ENNReal) / 3 + 1 / 3) + 1 / 3 = 1 := by
  -- This requires more complex fraction addition handling
  ennreal_fraction_add

end FractionAddTests

/--
Main ENNReal arithmetic tactic that combines multiple specialized tactics.

This is the primary entry point for ENNReal arithmetic automation. It attempts
to solve goals involving ENNReal expressions by trying a sequence of specialized
tactics in order:

1. `ennreal_basic_simp` - Basic arithmetic simplification
2. `ennreal_div_self` - Division by self patterns
3. `ennreal_mul_cancel` - Multiplication cancellation in fractions
4. `ennreal_mul_div_assoc` - Multiplication/division associativity
5. `ennreal_inv_transform` - Inverse pattern transformations
6. `ennreal_fraction_add` - Fraction addition and simplification

The tactic will try each approach in sequence until one succeeds, or fail
with a descriptive error message if none apply.
-/
syntax "ennreal_arith" : tactic

elab_rules : tactic | `(tactic| ennreal_arith) => do
  let tactics : TSyntax `tactic := ← `(tactic| first
    | ennreal_div_self
    | ennreal_mul_cancel
    | ennreal_basic_simp


    | ennreal_fraction_add
    | ennreal_mul_div_assoc
    | ennreal_inv_transform

    | fail "ennreal_arith could not solve the goal")

  evalTactic tactics

section Tests

lemma test123: ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_arith

lemma test_main_tactic_addition : (↑2 : ENNReal) + ↑3 = ↑5 := by ennreal_arith

lemma test_addition_multiplication_precedence : (↑2 : ENNReal) + ↑3 * ↑4 = ↑14 := by ennreal_arith

lemma test_multiplicative_additive_identity {a : ℕ} : (↑a : ENNReal) * 1 + 0 = ↑a := by ennreal_arith

example: (18 : ENNReal) / 18 = 1 := by ennreal_arith

example: @Eq ENNReal (18 / 18) 1 := by
  ennreal_arith

-- Test the exact pattern from user's error
example : @HDiv.hDiv ENNReal ENNReal ENNReal instHDiv 18 18 = @OfNat.ofNat ENNReal 1 One.toOfNat1 := by ennreal_arith

lemma test_division_self_nonzero_global {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
   ennreal_arith

lemma test_multiplication_cancellation_right {a b c : ℕ} (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith

lemma test_mul_div_associativity {a b c : ℕ} :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
   ennreal_arith -- Should be handled by ennreal_arith

example: (@OfNat.ofNat ℝ≥0∞ 18 instOfNatAtLeastTwo)⁻¹ + 9⁻¹ = ( 6⁻¹ : ENNReal) := by
  ennreal_fraction_add

lemma test_mixed_arithmetic_operations : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

lemma test_zero_absorbing_properties : (0 : ENNReal) + 5 * 0 + 0 / 3 = 0 := by ennreal_arith
lemma test_one_identity_chain {a : ℕ} : (↑a : ENNReal) * 1 / 1 * 1 = ↑a := by ennreal_arith

lemma test_simple_arithmetic: (2 : ENNReal) + 3 = 5 := by ennreal_arith

-- Complex expression tests
lemma test_complex_expression_1 : ((↑2 : ENNReal) + ↑3) * (↑4 + ↑5) / ↑9 = ↑45 / ↑9 := by ennreal_arith


-- Edge case: all zeros
lemma test_all_zeros : (0 : ENNReal) + 0 * 0 / 1 = 0 := by ennreal_arith



-- Inverse and division mix
lemma test_inv_div_mix {a b : ℕ} : (↑a : ENNReal)⁻¹ / (↑b : ENNReal)⁻¹ = ↑b / ↑a := by
  -- This requires more complex inverse handling
  sorry

-- Test case from user's density_sum_one proof that currently fails
-- This test demonstrates the issue where ennreal_arith can't prove 18/18 = 1
-- after simplifying a complex nested addition
lemma test_nested_addition_division_fails :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
 ennreal_arith -- sorry -- ennreal_arith fails here!

-- The core issue: ennreal_arith fails on concrete division after simplification
lemma test_concrete_division_18_fails : (18 : ENNReal) / 18 = 1 := by
  ennreal_arith -- fails here!

-- But ennreal_fraction_add succeeds on the same goal
lemma test_nested_addition_division_fraction_add_succeeds :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  ennreal_fraction_add

-- Manual proof showing what should work
lemma test_concrete_division_18_manual : (18 : ENNReal) / 18 = 1 := by
  apply ENNReal.div_self <;> norm_num

-- This simulates what happens in the user's proof after split_ifs
-- The first ennreal_arith simplifies the nested sum but then fails on 18/18 = 1
lemma test_simulating_user_issue :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  -- First attempt: ennreal_arith partially succeeds by using norm_num to simplify to 18/18 = 1
  -- but then fails to prove that final step
  ennreal_arith
  -- sorry -- Replace with: ennreal_arith (this would fail with "18 / 18 = 1" remaining)

-- Test showing the workaround pattern from the user
lemma test_user_workaround :
  ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18 = 1 := by
  -- This mimics the user's solution of calling ennreal_arith multiple times
  first | ennreal_arith


-- Test simulating split_ifs with multiple goals
lemma test_split_ifs_simulation (p q : Prop) [Decidable p] [Decidable q] :
  (if p then (0 : ENNReal) else if q then 1/18 else
    ((1 : ENNReal) + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (2 + (2 + (1 + 1))))))))))) / 18) =
  (if p then 0 else if q then 1/18 else 1) := by
  split_ifs <;> ennreal_arith


end Tests

end ENNRealArith
