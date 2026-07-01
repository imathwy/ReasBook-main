import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item identifies partial quadratic convex functions directly by the
  canonical support-cut presentation `branch.toWithTopBotOn M` with quadratic branch
  `branch x = Q x + φ x` on a nonempty affine support `M`.
- `core/canonical`: the owner predicates are the chapter declarations `Function.IsConvex` and
  `Function.IsProper`, the source-facing owner predicate `Function.IsPartiallyQuadratic`, the
  chapter support-cut owner `Function.toWithTopBotOn` together with its source-facing bridge
  `branch.toWithTopBot + δ(· | support)`, the codomain lift `Function.toWithTopBot`, together
  with the structural objects `QuadraticForm 𝕜 E`, `AffineSubspace 𝕜 E`, and `AffineMap 𝕜 E 𝕜`.
- `bridge/view`: coordinate finite-dimensional normal forms belong in downstream bridge files; this
  item keeps the source owner at the intrinsic support-cut layer and does not expose a `Fin n` API.
- Primitive data vs derived API:
  - primitive data: a `𝕜`-valued quadratic branch `fun x ↦ Q x + φ x` together with an affine
    support subspace `M`, with nonemptiness recorded intrinsically as `(M : Set E).Nonempty`;
  - owner-side consequences: `Function.IsConvex f` and `Function.IsProper f`;
  - derived API: the support-cut presentation
    `branch.toWithTopBotOn support`,
    and the owner consequences `f.IsConvex 𝕜` and `f.IsProper`.

Domain-style sampling used here:
- `QuadraticForm 𝕜 E` from mathlib;
- `AffineSubspace 𝕜 E` from mathlib;
- `AffineMap 𝕜 E 𝕜` from mathlib;
- `Function.toWithTopBotOn`, `indicatorFunction`, its notation `δ(· | C)`, and
  `Function.toWithTopBot` from the earlier chapter support-cut layer;
- `Function.isConvex_toWithTopBotOn_iff` from Remark 4.4.5.

Layer target:
- the source-facing owner layer is the predicate `Function.IsPartiallyQuadratic`, whose primitive
  content is the intrinsic support-cut presentation on the ordered commutative scalar module/affine
  ambient rather than a chosen finite-coordinate realization.
- this file keeps only that intrinsic owner layer; concrete coordinate normal forms are
  downstream bridge views.
-/

section Owner

variable {𝕜 : Type*} [CommRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

namespace Function

variable {f : E → WithTopBot 𝕜}

section OwnerLayer

variable [LE 𝕜]

/-- Owner alias for partial quadratic functions: the canonical support-cut extension of a
nonnegative quadratic-plus-affine `𝕜`-branch to `WithTopBot 𝕜` along a nonempty affine
subspace. -/
abbrev IsPartiallyQuadratic (f : E → WithTopBot 𝕜) : Prop :=
  ∃ (Q : QuadraticForm 𝕜 E) (φ : E →ᵃ[𝕜] 𝕜) (M : AffineSubspace 𝕜 E),
    (∀ x, 0 ≤ Q x) ∧ (M : Set E).Nonempty ∧
      f = (fun x ↦ Q x + φ x).toWithTopBotOn M

/-- Text 12.3.3 at the intrinsic owner layer: a function is partially quadratic exactly when it
is a support-cut extension of a nonnegative quadratic-plus-affine branch along a nonempty affine
support subspace. -/
theorem isPartiallyQuadratic_iff
    (f : E → WithTopBot 𝕜) :
    f.IsPartiallyQuadratic ↔
      ∃ (Q : QuadraticForm 𝕜 E) (φ : E →ᵃ[𝕜] 𝕜) (M : AffineSubspace 𝕜 E),
        (∀ x, 0 ≤ Q x) ∧ (M : Set E).Nonempty ∧
          f = (fun x ↦ Q x + φ x).toWithTopBotOn M := by
  rfl

end OwnerLayer

namespace IsPartiallyQuadratic

section Convex

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Any function admitting the source-facing partial-quadratic support-cut presentation is
convex. -/
theorem isConvex (hf : f.IsPartiallyQuadratic) :
    f.IsConvex 𝕜 := sorry

end Convex

section Proper

variable [Preorder 𝕜]

/-- Any function admitting the source-facing partial-quadratic support-cut presentation is
proper. -/
theorem isProper (hf : f.IsPartiallyQuadratic) :
    f.IsProper := sorry

end Proper

end IsPartiallyQuadratic

end Function

end Owner
