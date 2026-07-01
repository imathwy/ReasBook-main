import Lake
open Lake DSL System

package «SmoothManifoldsLee» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

lean_lib SmoothManifoldsLee where
