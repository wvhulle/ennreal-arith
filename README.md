# Arithmetic simplification for ENNReal

This library provides a convenience tactic for ENNReal (extended non-negative real) arithmetic. ENNReal appears frequently in Mathlib's probability theory and measure theory.

## Installation

Add this project as a dependency to your `lakefile.toml`:

```toml
[[require]]
scope = "wvhulle"
name = "ennreal-arith"
rev = "main" # or a specific commit
```

Or if you use `leanfile.lean`, 

```lean
import Lake
open Lake DSL 

require «ennreal-arith» from git
  "https://github.com/wvhulle/ennreal-arith.git" @ "[COMMIT_HASH]"
```


## Usage

Import in your Lean files:

```lean
import ENNRealArith
```

Use the `ennreal_arith` tactic which combines multiple simplification strategies:

```lean
example : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by ennreal_arith

example (a : ℕ) (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by ennreal_arith

example (a b c : ℕ) (hc : c ≠ 0) : 
  (↑(a * c) : ENNReal) / (↑(b * c)) = ↑a / ↑b := by ennreal_arith
```

## Testing

To run unit and integration tests, use the following command:

```bash
lake test
```