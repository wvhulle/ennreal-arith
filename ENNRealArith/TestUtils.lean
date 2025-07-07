import Mathlib.Data.ENNReal.Basic
import ENNRealArith.Common

namespace ENNRealArith

/-!
# Common Test Utilities for ENNReal Arithmetic

This module provides common test patterns and helper lemmas used across all
ENNReal arithmetic tactic modules.

Note: The current implementation focuses on `ℕ` to `ENNReal` coercions, which is
the most common use case. Future generalizations could extend to other numeric
types like `ℚ≥0` or abstract semirings, but would require careful consideration
of the mathematical properties that make these tactics work.
-/

section IdentityTests

/-- Test zero as additive identity -/
def test_zero_additive_identity (a : ℕ) : Prop := (↑a : ENNReal) + 0 = ↑a

/-- Test one as multiplicative identity -/
def test_one_multiplicative_identity (a : ℕ) : Prop := (↑a : ENNReal) * 1 = ↑a

/-- Test division by one identity -/
def test_division_by_one_identity (a : ℕ) : Prop := (↑a : ENNReal) / 1 = ↑a

end IdentityTests

section ConcreteArithmetic

/-- Common concrete test numbers -/
def test_numbers : List ℕ := [2, 3, 5, 6, 7, 18]

/-- Test addition preservation for natural number casts -/
def test_addition_preserves_cast (a b : ℕ) : Prop := 
  (↑a : ENNReal) + (↑b : ENNReal) = ↑(a + b : ℕ)

/-- Test multiplication preservation for natural number casts -/
def test_multiplication_preserves_cast (a b : ℕ) : Prop := 
  (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ)

end ConcreteArithmetic

section DivisionTests

/-- Test division by self for nonzero numbers -/
def test_division_by_self (a : ℕ) (ha : a ≠ 0) : Prop := 
  (↑a : ENNReal) / ↑a = 1

/-- Test zero division property -/
def test_zero_division (a : ℕ) : Prop := 
  (0 : ENNReal) / ↑a = 0

end DivisionTests

end ENNRealArith