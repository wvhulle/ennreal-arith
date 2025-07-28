{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    # Elan - Lean version manager
    elan
    
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
    # Setup pre-commit hook if it doesn't exist
    if [ ! -f .git/hooks/pre-commit ] && [ -d .git ]; then
      mkdir -p .git/hooks
      cp scripts/pre-commit .git/hooks/pre-commit
      chmod +x .git/hooks/pre-commit
      echo "✅ Pre-commit hook installed"
    fi
  '';

  # Environment variables
  LEAN_PATH = "";
  
  # Inform direnv about the shell
  NIX_SHELL_PRESERVE_PROMPT = 1;
}