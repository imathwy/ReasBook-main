import Lake
open Lake DSL System

package «Serre» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

lean_lib Serre where
