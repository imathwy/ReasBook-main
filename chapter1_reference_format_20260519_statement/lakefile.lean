import Lake
open Lake DSL System

package «chapter1_reference_format» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

lean_lib chapter1_reference_format where
