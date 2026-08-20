import Lake
open Lake DSL

package «ReasBook» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`weak.linter.style.longLine, false⟩,
    ⟨`weak.linter.style.emptyLine, false⟩,
    ⟨`weak.linter.style.cdot, false⟩,
    ⟨`weak.linter.style.maxHeartbeats, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

-- Register doc-gen4's `docs` facet in this main project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.0"

require subverso from git "https://github.com/leanprover/subverso" @ "verso-v4.32.0"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «ReasBook» where

-- Books from ALLBOOKS (sources live under Books/<LibName>/)
lean_lib ComputationalMethodsInverseProblems_Vogel_2002 where
  srcDir := "Books"

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true