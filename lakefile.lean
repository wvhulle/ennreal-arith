import Lake
open Lake DSL

package «ennreal-arith» where
  version := v!"0.0.1"
  keywords := #["probability", "ENNReal", "arithmetic", "tactics"]
  description := "Arithmetic tactics for extended non-negative real numbers (ENNReal)"
  homepage := "https://github.com/wvhulle/ennreal-arith"
  license := "Apache-2.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ENNRealArith» where
  -- Glob patterns for the library's Lean sources
  globs := #[.andSubmodules `ENNRealArith]
  -- Additional options for this library
  moreLeanArgs := #[]

@[test_driver]
lean_lib «ENNRealTest» where
  globs := #[.andSubmodules `ENNRealTest]
  -- This library depends on ENNRealArith
  needs := #[ENNRealArith]
  moreLinkArgs := #[]
