import Lake

open Lake DSL System

def mathlibRoot : FilePath :=
  FilePath.mk ".." / "stacks-proof" / ".lake" / "packages" / "mathlib"

package stacks_project where
  moreLeanArgs := #["-j", "1"]
  restoreAllArtifacts := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.style.longLine, false⟩,
    ⟨`weak.linter.style.emptyLine, false⟩,
    ⟨`weak.linter.style.cdot, false⟩,
    ⟨`weak.linter.style.maxHeartbeats, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩
  ]

require mathlib from
  mathlibRoot

@[default_target]
lean_lib stacks_project where
  srcDir := FilePath.mk "."
