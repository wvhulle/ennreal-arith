# Development Setup

This project uses Nix and direnv for reproducible development environments.

## Quick Start

1. **Install direnv** (if not already installed):
   ```bash
   # On NixOS, direnv should already be available
   nix-env -iA nixpkgs.direnv
   ```

2. **Allow direnv in this directory**:
   ```bash
   direnv allow
   ```

3. **Start development**:
   The environment will automatically load with Lean 4, Lake, and all dependencies.

## What's Included

- **Elan** (Lean version manager) - respects project's `lean-toolchain` file
- **Pre-commit hooks** that automatically:
  - Build the project (`lake build`)
  - Run all tests (`lake test`)
  - Prevent commits if build or tests fail
- **Development tools**: git, bash, coreutils

## Pre-commit Hook

The pre-commit hook is automatically installed when you enter the Nix shell. It will:

1. ✅ Verify you're in a Lean project directory
2. 🔨 Build the project with `lake build`
3. 🧪 Run tests with `lake test`
4. 📋 Show which Lean files are being committed
5. ❌ Block the commit if build or tests fail

### Manual Hook Testing

You can test the pre-commit hook manually:
```bash
.git/hooks/pre-commit
```

### Bypassing Hook (Emergency Only)

If you need to commit without running checks:
```bash
git commit --no-verify -m "emergency commit"
```

## Files

- `shell.nix`: Nix shell environment definition
- `.envrc`: direnv configuration
- `.git/hooks/pre-commit`: Pre-commit hook script (auto-generated)

## Troubleshooting

**Hook not running?**
- Check that `.git/hooks/pre-commit` exists and is executable
- Re-enter the shell: `direnv reload`

**Build failing?**
- Make sure all dependencies are in `lakefile.lean`
- Check for syntax errors in `.lean` files

**Tests failing?**
- Run `lake test` manually to see detailed error output
- Fix failing test cases before committing