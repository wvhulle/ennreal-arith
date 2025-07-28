{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    # Lean 4 and Lake
    lean4
    
    # Git for version control
    git
    
    # Shell utilities
    bash
    coreutils
    
    # Development tools
    direnv
    
    # Pre-commit framework
    pre-commit
  ];

  shellHook = ''
    echo "Entering Lean 4 development environment..."
    echo "Lean version: $(lean --version)"
    echo "Lake version: $(lake --version)"
    
    # Setup pre-commit hooks automatically
    if [ ! -f .git/hooks/pre-commit ]; then
      echo "Setting up pre-commit hook..."
      mkdir -p .git/hooks
      cat > .git/hooks/pre-commit << 'EOF'
#!/usr/bin/env bash
set -e

echo "🔍 Running pre-commit checks..."

# Check if we're in the correct directory
if [ ! -f "lakefile.lean" ]; then
    echo "❌ Not in a Lean project directory (lakefile.lean not found)"
    exit 1
fi

# Build the project
echo "🔨 Building project..."
if ! lake build; then
    echo "❌ Build failed!"
    exit 1
fi
echo "✅ Build successful!"

# Run tests
echo "🧪 Running tests..."
if ! lake test; then
    echo "❌ Tests failed!"
    exit 1
fi
echo "✅ Tests passed!"

# Check for any uncommitted changes to critical files
if git diff --cached --name-only | grep -E "\.(lean|toml)$" > /dev/null; then
    echo "📋 Lean files being committed:"
    git diff --cached --name-only | grep -E "\.(lean|toml)$" | sed 's/^/  - /'
fi

echo "🎉 All pre-commit checks passed!"
echo "Ready to commit!"
EOF
      chmod +x .git/hooks/pre-commit
      echo "Pre-commit hook installed successfully!"
    else
      echo "Pre-commit hook already exists."
    fi
    
    # Check if we're in a git repository
    if [ -d .git ]; then
      echo "Git repository detected."
    else
      echo "Warning: Not in a git repository."
    fi
    
    echo "Ready for development!"
  '';

  # Environment variables
  LEAN_PATH = "";
  
  # Inform direnv about the shell
  NIX_SHELL_PRESERVE_PROMPT = 1;
}