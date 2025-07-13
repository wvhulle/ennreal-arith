# Arithmetic simplification for ENNReal

ENNReal appears frequently in Mathlib's probability theory and measure theory. This library provides a convenience tactic `eq_as_reals` for ENNReal (extended non-negative real) numbers or arithmetic expressions. 

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

Use the `eq_as_reals` tactic to prove equality of probabilities (`ENNReal` in Mathlib4), lifted into the real numbers:

```lean
example : (↑2 : ENNReal) * 1 + ↑3 * 0 + ↑5 = ↑7 := by eq_as_reals

example (a : ℕ) (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by eq_as_reals

example (a b c : ℕ) (hc : c ≠ 0) : 
  (↑(a * c) : ENNReal) / (↑(b * c)) = ↑a / ↑b := by eq_as_reals
```

## Testing

To run unit and integration tests, use the following command:

```bash
lake test
```