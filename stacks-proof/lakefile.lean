import Lake
open Lake DSL System

package stacks_project where
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

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

@[default_target]
lean_lib stacks_project where
  srcDir := FilePath.mk "."

lean_lib P2512_19197 where

lean_lib stacks_proof where
