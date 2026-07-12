import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Definition 17.0.2 recalls the chapter surface `conv[𝕜] s` together with the two
  immediate textbook views used downstream: finite convex-combination membership and minimality
  among convex supersets.
- `core/canonical`: the owner abstraction is `convexHull 𝕜 s`.
- `bridge/view`: the primitive closure-operator package on the chapter surface is recalled through
  `Set.subset_conv`, `Set.convex_conv`, `Set.conv_subset`, and `Set.conv_subset_iff`; the
  definition-level
  intersection characterization is then recalled in primitive binder form `Set.conv_eq_iInter`
  with the textbook set-of-sets surface `Set.conv_eq_sInter` as a display bridge; chapter-surface
  finite-combination membership is recalled first in intrinsic simplex-owner form
  (`Set.mem_conv_iff_exists_stdSimplex`), with direct finite weighted-sum form
  (`Set.mem_conv_iff_exists_fintype`) retained as a source-facing bridge view.
- Domain-style sampling used here: `convexHull`, `Set.mem_conv_iff_exists_stdSimplex`,
  `Set.mem_conv_iff_exists_fintype`, `Set.subset_conv`, `Set.convex_conv`, `Set.conv_subset`,
  `Set.conv_subset_iff`, `Set.conv_eq_iInter`, and `Set.conv_eq_sInter`.
- Primitive data vs derived API: no new primitive data belongs here. The convex hull itself is the
  canonical object `convexHull`; at the chapter level, `Set.subset_conv`, `Set.convex_conv`,
  `Set.conv_subset`, and `Set.conv_subset_iff` are the primitive closure-package bridges, while
  `Set.conv_eq_iInter`, `Set.conv_eq_sInter`, and finite weighted-sum membership are derived
  views reused directly.
- Layer target: source-facing `conv[𝕜]` notation and canonical owner lemmas over the same
  `convexHull` layer, with no parallel Chapter 4 wrapper.

Abstraction checks for this item:
- Codomain concreteness: not applicable. This item is set-valued (`Set E`) and introduces no
  ordered-extended codomain such as `EReal`.
- Scalar/ambient structure: no concrete scalar or model is fixed here; the recalled owner/bridges
  stay parametric in `𝕜` and the ambient space under their canonical mathlib assumptions.
- Owner choice: intrinsic owner is `convexHull`; chapter notation `conv[𝕜] s` is retained only as
  the canonical bridge surface.
- Ambient vs intrinsic topology: not applicable. This item has no `closure`/`interior` or relative
  topology claim.
- Owner naming and notation: keep the short owner `convexHull` and the mathematically primary
  notation `conv[𝕜] s`; use short chapter bridge names (`Set.subset_conv`, `Set.convex_conv`,
  `Set.conv_subset`, `Set.conv_subset_iff`) on the public surface rather than raw owner names.
-/

/- Definition 17.0.2 reuses the canonical convex-hull owner `convexHull`; chapter notation
`conv[𝕜] s` is a definitional bridge to this owner. -/
recall convexHull

/- Primitive closure-package bridge: every set is contained in its chapter-surface convex hull. -/
recall Set.subset_conv

/- Primitive closure-package bridge: the chapter-surface convex hull is convex. -/
recall Set.convex_conv

/- Primitive closure-package bridge: any convex superset of `S` contains `conv[𝕜] S`. -/
recall Set.conv_subset

/- Primitive closure-package bridge in iff form. -/
recall Set.conv_subset_iff

/- Primitive definition-level bridge in binder form: `conv[𝕜] s` is the intersection of all convex
supersets of `s`. -/
recall Set.conv_eq_iInter

/- Textbook set-of-sets display of the same intersection definition. -/
recall Set.conv_eq_sInter

/- Finite convex-combination membership on the chapter surface in intrinsic simplex-owner form. -/
recall Set.mem_conv_iff_exists_stdSimplex

/- Finite convex-combination membership on the chapter surface in direct `Fintype` weighted-sum
bridge form. -/
recall Set.mem_conv_iff_exists_fintype
