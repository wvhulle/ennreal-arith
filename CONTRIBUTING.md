# Contributing

## Development setup

1. Install direnv: `nix-env -iA nixpkgs.direnv`
2. Allow direnv: `direnv allow`
3. The environment loads automatically with Lean 4, Lake, and dependencies

## Testing

Run `lake test` to build and run all tests.

## Pre-commit hook

Automatically installed when entering the shell. Runs `lake build` and `lake test` before each commit.