import Lake
open Lake DSL System

package «OptimizationResearch» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

@[default_target]
lean_lib OptimizationResearch where

