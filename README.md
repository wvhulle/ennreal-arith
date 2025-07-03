# Arithmetic simplification tactic for ENNReal

This tactic will help simplifying ordinary expressions of ENNReal numbers. This type of number appears in Mathlib's probability theory.

To use this tactic in a Lean4 project, you have to add this project as a dependency to you `lakefile.toml`:

```toml
[[require]]
scope = "wvhulle"
name = "ennreal-arith"
```

Then, you can import the tactic in your Lean files:

```lean
import ENNRealArith

example (a b c : ENNReal) : a + b - c = a + (b - c) := by
    ennreal_arith
```