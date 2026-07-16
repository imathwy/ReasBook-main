# Bootstrap Error Report

**Date**: 2026-07-07
**Mode**: Initialization — post-universe-dedup, pre-API-fix
**Status**: 0/19 books compile

## Summary

- Universe dedup: ✅ 1,225 files fixed, 6,607 duplicate declarations removed
- All 19 books + 2 papers activated in ReasBook.lean
- Remaining errors: primarily `unknown identifier` (toolchain-gap from ALLBOOKS origins)

## Books with errors

### AlgebraicTopology_May_1999 (1,431 errors)
- **unknown_identifier**: `standardLoopClass`, `standardLoopClass_one_zpowers_eq_top`, `brouwer_fixed_point_closed_unit_disk`, `fundamental_group_map_homotopy_commutes`, `polynomialNormalizedBoundaryMap`
- **unknown_namespace**: `CircleDegree`
- **instance_failure**: cascading from unknown identifiers

### StacksProject_2024 (5,400+ errors)
- **unknown_identifier**: `topologicalKrullDimAt`, `Module.CohenMacaulay`, `IsCatenaryRing`, `UniversallyCatenaryRing`, `CohenMacaulayRing`, `Module.mem_support_localizationAtPrime_iff`
- **unsolved_goals**: cascading
- **missing_module**: various missing imports

### CombinatorialGroupTheory_Magnus_2004 (4 errors fixed, more remain)
- **unknown_identifier**: `IsHopfian`, `MonoidHom.injective_of_surjective`

### LecturesConvexOptimization_Nesterov_2018 (100+ errors)
- **unknown_identifier**: `mem_centerCutEllipsoid_iff`

### LinearRepresentations_Serre_1977
- **unknown_identifier**: various module/representation API changes

### ReasLib
- **missing_module**: `Mathlib.LinearAlgebra.Matrix.Spectrum` (removed in v4.30.0)

## Safe Fixes Applied

| Fix | Count |
|------|:---:|
| Universe dedup | 6,607 declarations in 1,225 files |
| (none beyond universe — all remaining are unknown identifiers) | — |

## Cannot Fix — Needs Migration Table Updates

All remaining errors are `unknown identifier` / `unknown constant` / `unknown namespace`.
These need manual lookup in mathlib v4.30.0 docs to find replacements, then
entries added to `scripts/lib/migration_table.py`.

Priority order (by impact):
1. `Mathlib.LinearAlgebra.Matrix.Spectrum` — blocks ReasLib entirely, module removed
2. StacksProject identifiers — ~5,400 errors in one book
3. AlgebraicTopology identifiers — blocks the first book in the import chain
4. Nesterov, Magnus, Serre identifiers
