# Arithmetic simplification for ENNReal

This library provides additional simp lemmas and a convenience tactic for ENNReal (extended non-negative real) arithmetic. ENNReal appears frequently in Mathlib's probability theory and measure theory.

## Installation

Add this project as a dependency to your `lakefile.toml`:

```toml
[[require]]
scope = "wvhulle"
name = "ennreal-arith"
```

## Usage

Import the library in your Lean files:

```lean
import ENNRealArith
```

### Additional simp lemmas

The library adds simp lemmas for ENNReal patterns not covered by Mathlib:

```lean
-- Division by self for successors (always non-zero)
example (n : ℕ) : (↑(n + 1) : ENNReal) / ↑(n + 1) = 1 := by 
  exact ENNRealArith.ennreal_succ_div_self n

-- Multiplication and division associativity
example (a b c : ℕ) : 
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by simp

-- Multiplication cancellation (requires non-zero proof)
example (a b c : ℕ) (hc : c ≠ 0) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = ↑a / ↑b := by 
  simp [ENNRealArith.ennreal_nat_mul_div_mul_right hc]
```

### Working with `norm_cast` and `norm_num`

The standard tactics continue to work as before, handling coercions and numeric computations:

```lean
-- norm_cast handles coercions
example (a b : ℕ) : (↑a : ENNReal) + ↑b = ↑(a + b) := by norm_cast

-- norm_num evaluates numeric expressions
example : (↑2 : ENNReal) + ↑3 = ↑5 := by norm_num
```

### Convenience tactic: `ennreal_arith`

For complex expressions, use the `ennreal_arith` tactic which combines multiple simplification strategies:

```lean
example : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

example (a : ℕ) (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

example (a b c : ℕ) (hc : c ≠ 0) : 
  (↑(a * c) : ENNReal) / (↑(b * c)) = ↑a / ↑b := by ennreal_arith
```

## What this library provides

The library consists of:

1. **Simp lemmas** (`ENNRealArith.Simp`): Additional `@[simp]` lemmas for ENNReal patterns like:
   - Division by self for natural numbers
   - Multiplication cancellation in fractions
   - Multiplication/division associativity
   
2. **Convenience tactic** (`ennreal_arith`): Combines multiple approaches to solve complex expressions:
   - Tries various combinations of `norm_num`, `norm_cast`, and `simp`
   - Includes specialized sub-tactics for division, multiplication cancellation, and inverse patterns
   - Useful when the standard tactics alone don't suffice

Note: Lean's existing `norm_cast` and `norm_num` already handle ENNReal coercions and basic arithmetic well. This library adds patterns specific to division and multiplication that aren't covered by the standard tactics.