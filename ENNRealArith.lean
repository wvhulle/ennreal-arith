import ENNRealArith.Basic

/-!
# ENNReal Arithmetic Simplification

This library provides simp lemmas and a convenience tactic for ENNReal arithmetic.

## What this library provides

1. **Additional simp lemmas** for ENNReal patterns that aren't in Mathlib:
   - Division by self for natural numbers: `(↑(n + 1) : ENNReal) / ↑(n + 1) = 1`
   - Multiplication cancellation: `(↑(a * c) : ENNReal) / (↑(b * c)) = ↑a / ↑b`
   - Multiplication/division associativity: `↑a * (↑b / ↑c) = ↑(a * b) / ↑c`
   - Various other simplification patterns

2. **Convenience tactic** `ennreal_arith` that combines multiple approaches:
   - Tries `norm_num`, `norm_cast`, `simp` in various combinations
   - Handles division by self, multiplication cancellation, and inverse patterns
   - Useful for complex expressions that need multiple simplification steps

## Examples

```lean
import ENNRealArith

-- Our simp lemmas work automatically:
example (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by 
  exact ennreal_succ_div_self n

example (a b c : ℕ) : 
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by 
  simp

-- The convenience tactic handles complex expressions:
example : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

example (a : ℕ) (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith
```

Note: Lean's existing `norm_cast` and `norm_num` already handle ENNReal well for basic
arithmetic and coercions. This library adds patterns specific to division and 
multiplication that aren't covered by the standard tactics.
-/
