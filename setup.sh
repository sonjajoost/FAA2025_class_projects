#!/bin/bash

# Setup script for FAA2025 Class Projects Repository
set -e

echo "Setting up FAA2025 Class Projects Repository..."

if [ ! -d ".git" ]; then
    echo "Error: Not in a git repository."
    exit 1
fi

echo "Creating lean-toolchain..."
cat > lean-toolchain << 'EOF'
leanprover/lean4:v4.25.0
EOF

echo "Creating lakefile.lean..."
cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package «FAA2025_class_projects» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib «Projects» where
  globs := #[.submodules `Projects]
EOF

echo "Creating project structure..."
mkdir -p Projects/Project1
mkdir -p .github/workflows

echo "Creating example template..."
cat > Projects/Project1/Template.lean << 'EOF'
/-
  Project 1 Template
  
  Complete the proofs below.
-/

import Mathlib.Tactic

theorem example_theorem (a b : Nat) : a + b = b + a := by
  sorry
EOF

echo "Creating CI workflow..."
cat > .github/workflows/lean-check.yml << 'EOF'
name: Lean CI

on:
  push:
    branches: ['**']
  pull_request:
    branches: [main]

jobs:
  build-and-check:
    runs-on: ubuntu-latest
    timeout-minutes: 30
    
    steps:
      - name: Checkout
        uses: actions/checkout@v4
      
      - name: Install elan
        run: |
          curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      
      - name: Print versions
        run: |
          echo "### Lean Toolchain" >> $GITHUB_STEP_SUMMARY
          cat lean-toolchain >> $GITHUB_STEP_SUMMARY
          lean --version
          lake --version
      
      - name: Cache dependencies
        uses: actions/cache@v4
        with:
          path: .lake
          key: ${{ runner.os }}-lake-${{ hashFiles('lakefile.lean', 'lean-toolchain', 'lake-manifest.json') }}
          restore-keys: ${{ runner.os }}-lake-
      
      - name: Update dependencies
        run: |
          lake update
          lake exe cache get || echo "Cache unavailable"
      
      - name: Build
        id: build
        run: |
          echo "### Build Status" >> $GITHUB_STEP_SUMMARY
          if lake build 2>&1 | tee build.log; then
            echo "Build: SUCCESS" >> $GITHUB_STEP_SUMMARY
          else
            echo "Build: FAILED" >> $GITHUB_STEP_SUMMARY
            echo '```' >> $GITHUB_STEP_SUMMARY
            tail -n 50 build.log >> $GITHUB_STEP_SUMMARY
            echo '```' >> $GITHUB_STEP_SUMMARY
            exit 1
          fi
      
      - name: Count sorry
        if: always()
        run: |
          echo "### Sorry Count" >> $GITHUB_STEP_SUMMARY
          SORRY_COUNT=$(grep -r "sorry" --include="*.lean" Projects/ 2>/dev/null | wc -l || echo "0")
          echo "Total: $SORRY_COUNT" >> $GITHUB_STEP_SUMMARY
          
          if [ "$SORRY_COUNT" -gt 0 ]; then
            echo "" >> $GITHUB_STEP_SUMMARY
            echo "<details><summary>Locations</summary>" >> $GITHUB_STEP_SUMMARY
            echo "" >> $GITHUB_STEP_SUMMARY
            echo '```' >> $GITHUB_STEP_SUMMARY
            grep -rn "sorry" --include="*.lean" Projects/ 2>/dev/null >> $GITHUB_STEP_SUMMARY || true
            echo '```' >> $GITHUB_STEP_SUMMARY
            echo "</details>" >> $GITHUB_STEP_SUMMARY
          fi
      
      - name: Check axioms
        if: always()
        run: |
          echo "### Axiom Check" >> $GITHUB_STEP_SUMMARY
          
          # Check for custom axiom definitions (not allowed)
          if grep -r "^axiom " --include="*.lean" Projects/ 2>/dev/null; then
            echo "FAILED: Custom axioms detected (not allowed)" >> $GITHUB_STEP_SUMMARY
            echo '```' >> $GITHUB_STEP_SUMMARY
            grep -rn "^axiom " --include="*.lean" Projects/ 2>/dev/null >> $GITHUB_STEP_SUMMARY || true
            echo '```' >> $GITHUB_STEP_SUMMARY
            exit 1
          else
            echo "No custom axioms" >> $GITHUB_STEP_SUMMARY
          fi
          
          # Report Classical axiom usage (informational)
          echo "" >> $GITHUB_STEP_SUMMARY
          echo "<details><summary>Classical axioms (informational)</summary>" >> $GITHUB_STEP_SUMMARY
          echo "" >> $GITHUB_STEP_SUMMARY
          
          if grep -r "Classical\." --include="*.lean" Projects/ 2>/dev/null | head -20; then
            echo '```' >> $GITHUB_STEP_SUMMARY
            grep -rn "Classical\." --include="*.lean" Projects/ 2>/dev/null | head -20 >> $GITHUB_STEP_SUMMARY || true
            echo '```' >> $GITHUB_STEP_SUMMARY
          else
            echo "None found" >> $GITHUB_STEP_SUMMARY
          fi
          echo "</details>" >> $GITHUB_STEP_SUMMARY
      
      - name: Linter
        if: always()
        continue-on-error: true
        run: |
          echo "### Linter Warnings" >> $GITHUB_STEP_SUMMARY
          echo "To be configured" >> $GITHUB_STEP_SUMMARY
      
      - name: Summary
        if: always()
        run: |
          echo "" >> $GITHUB_STEP_SUMMARY
          echo "---" >> $GITHUB_STEP_SUMMARY
          echo "Branch: \`${{ github.ref_name }}\`" >> $GITHUB_STEP_SUMMARY
          echo "Commit: \`${{ github.sha }}\`" >> $GITHUB_STEP_SUMMARY
EOF

echo "Creating README..."
cat > README.md << 'EOF'
# FAA 2025 Class Projects

Formalization of Algorithms and Arithmetic - ETH Zurich

## Quick Start

```bash
git clone https://github.com/sorrachai/FAA2025_class_projects.git
cd FAA2025_class_projects
lake exe cache get
lake build
```

## Workflow

### Create your branch
```bash
git checkout -b project1-yourname
```

### Work on your project
Edit files in `Projects/ProjectN/`

### Test locally
```bash
lake build
```

### Submit
```bash
git add .
git commit -m "Complete Project 1"
git push origin project1-yourname
```

Then create a Pull Request on GitHub.

## CI Checks

Automatic checks on every push:

- **Build**: Must compile successfully
- **Sorry count**: Number of incomplete proofs
- **Axiom usage**: Custom axioms are not allowed
- **Linter**: Code quality warnings

## Project Structure

```
FAA2025_class_projects/
├── Projects/
│   ├── Project1/
│   └── Project2/
├── lakefile.lean
├── lean-toolchain
└── README.md
```

## Resources

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
EOF

echo "Creating .gitignore..."
cat > .gitignore << 'EOF'
/.lake/
/lake-packages/
/build/
*.olean
*.trace
/lake-manifest.json

.vscode/
.idea/
*.swp
*~
.DS_Store
EOF

echo ""
echo "Initializing Lake..."
if command -v lake &> /dev/null; then
    lake update
    lake exe cache get || echo "Warning: Cache download failed, will build from source"
else
    echo "Warning: lake not found. Run 'lake update' after installing elan."
fi

echo ""
echo "Setup complete. Next steps:"
echo "  git add ."
echo "  git commit -m \"Initial project setup\""
echo "  git push origin main"