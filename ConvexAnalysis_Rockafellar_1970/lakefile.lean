import Lake
open Lake DSL System

package «ConvexAnalysis» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

lean_lib ConvexAnalysis where

lean_lib ConvexAnalysis_Rockafellar_1970 where

lean_lib item_statement_json_runner where
