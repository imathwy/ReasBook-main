import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_5_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_5_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} {ι : Type u} {E : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable (f : ι → E → 𝕜) {C S : Set E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.6 is a family theorem for `𝕜`-valued functions convex on a
  relatively open set `C`, with two alternative boundedness hypotheses yielding the same
  conclusions on a compact subset `S ⊆ C`. Part (1) is the main source-facing theorem for
  the family owner hypothesis `PointwiseBoundedOn f C`; part (2) is a bridge theorem supplying a
  weaker source-visible hypothesis that upgrades canonically to that owner condition.
- `core/canonical`: the owner abstractions are the chapter family predicates
  `PointwiseBoundedOn`, `UniformlyBoundedOn`, and `EquiLipschitzOn`, together with the ambient
  finite-dimensional normed-space layer over `𝕜` already used by the upstream single-function owner
  theorem `Function.IsConvex.lipschitzOn_realBranch_on_compact_subset_riDom` in
  Theorem 10.4.
- `bridge/view`: Rockafellar's condition `conv (cl C') ⊇ C` is expressed on the intrinsic closure
  layer as `C ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 C')`, and the finiteness of the pointwise
  sup/inf over the family is
  rendered by `BddAbove` and `BddBelow` of the corresponding value sets in `𝕜`. The bridge theorem
  below upgrades those source hypotheses to `PointwiseBoundedOn f C`, after which part (2) reuses
  the owner theorem from part (1).

Domain-style sampling used here:
- `Function.IsConvex.lipschitzOn_realBranch_on_compact_subset_riDom` from
  Theorem 10.4;
- `ri[𝕜](C) = C` as the intrinsic relative-openness owner equation on theorem surfaces;
- `ConvexOn` for convex `𝕜`-valued functions on `C`, already carrying convexity of `C`;
- `PointwiseBoundedOn` for the strong hypothesis on the family over `C`;
- `UniformlyBoundedOn` for the common two-sided bound on `S`;
- `EquiLipschitzOn` for the common Lipschitz conclusion on `S`;
- `BddBelow` and `BddAbove` for finiteness of pointwise infima and suprema;
- `convexHull 𝕜 (intrinsicClosure 𝕜 C')` for Rockafellar's generating-set hypothesis.

Primitive data vs derived API:
- primitive inputs: the relatively open set `C`, the family `f`, convexity of each `f i`
  on `C`, a compact subset `S ⊆ C`, and one of the two source hypothesis alternatives; the
  closed-bounded `S` phrasing is kept as a source bridge into this compact owner layer;
- in the weaker alternative, the primitive source data remain theorem-level: a generating subset
  `C' ⊆ C` with pointwise upper bounds, and one point of `C` with a common lower bound;
- derived API: the chapter conclusions `UniformlyBoundedOn f S` and `EquiLipschitzOn f S`.

Layer target:
- clause (1) stays `source-facing`, stated directly with the chapter owner
  `PointwiseBoundedOn f C`;
- clause (2) is `bridge/view`, and should reuse clause (1) rather than introduce a parallel family
  wrapper.

Scalar/ambient minimality note:
- this item keeps scalar assumptions `[NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [CompleteSpace 𝕜]` because the reused Chapter 10 owner stack for convex families and compact-set
  Lipschitz control is currently available at that level in this project. The old
  closed/bounded-surface phrasing is retained only as a bridge theorem derived from compactness.
-/

variable (hC_ri : ri[𝕜](C) = C)
variable (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
variable (hS_compact : IsCompact S)
variable (hS_subset : S ⊆ C)

namespace PointwiseBoundedOn

-- Proof sketch: combine the pointwise boundedness hypothesis on `C` with the local boundedness
-- estimates for convex functions on relatively open convex sets, then apply the Chapter 10 compact
-- subset argument on `S` to obtain one common two-sided bound and one common
-- Lipschitz constant.
/-- Theorem 10.6 (1), in owner form: a pointwise bounded family of `𝕜`-valued functions convex on
a relatively open set `C` is uniformly bounded and equi-Lipschitz on every compact subset
`S ⊆ C`. The textbook `R^n` statement is the specialization of this owner-layer theorem to
`𝕜 := ℝ` and `E := EuclideanSpace ℝ (Fin n)`. -/
theorem uniformlyBoundedOn_and_equiLipschitzOn
    {f : ι → E → 𝕜} {C S : Set E} (hbound : PointwiseBoundedOn f C)
    (hC_ri : ri[𝕜](C) = C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hS_compact : IsCompact S) (hS_subset : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzOn f S := sorry

/-- Closed/bounded bridge corollary of Theorem 10.6 (1). -/
theorem uniformlyBoundedOn_and_equiLipschitzOn_of_isClosed_isBounded
    {f : ι → E → 𝕜} {C S : Set E} (hbound : PointwiseBoundedOn f C)
    (hC_ri : ri[𝕜](C) = C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    [ProperSpace E]
    (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) (hS_subset : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzOn f S := by
  exact hbound.uniformlyBoundedOn_and_equiLipschitzOn
    hC_ri hf_convex (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded) hS_subset

end PointwiseBoundedOn

section GeneratingUpperAndOneLower

variable (hupper : ∃ C' ⊆ C, C ⊆ convexHull 𝕜 (intrinsicClosure 𝕜 C') ∧
  ∀ x : C', BddAbove (range fun i ↦ f i x))
variable (hlower : ∃ x : C, BddBelow (range fun i ↦ f i x))

include hf_convex hupper hlower

-- Proof sketch: form the pointwise supremum of the family and use the generating-subset upper
-- bound together with Theorem 6.3 to show that supremum is finite on all of `C`. Combine this
-- with the one-point common lower bound and convexity to obtain two-sided bounds at every point of
-- `C`, i.e. the owner hypothesis `PointwiseBoundedOn f C`.
/-- Bridge theorem for Theorem 10.6: a generating subset of `C` carrying pointwise upper bounds,
together with one point of `C` carrying a common lower bound, upgrades canonically to the owner
hypothesis `PointwiseBoundedOn f C`. -/
theorem pointwiseBoundedOn_of_generating_upper_and_one_lower_bound
    :
    PointwiseBoundedOn f C := sorry

omit hf_convex hupper hlower

include hC_ri hf_convex hS_compact hS_subset hupper hlower

-- Proof sketch: form the pointwise supremum of the family, use the generating subset hypothesis and
-- Theorem 6.3 to show it is finite on `C`, apply Theorem 10.1 to get local upper bounds on `C`,
-- combine these with the one-point common lower bound and convexity to recover two-sided local
-- bounds, and conclude on compact `S`.
/-- Theorem 10.6 (2), as a bridge into clause (1): if `C` is a relatively open set, `S` is a
compact subset of `C`, and `f` is a family of `𝕜`-valued functions convex on `C` for
which there is a generating subset of `C` carrying pointwise upper bounds together with one point
of `C` carrying a common lower bound, then the family is uniformly bounded on `S` and
equi-Lipschitzian relative to `S`. -/
theorem uniformlyBoundedOn_and_equiLipschitzOn_of_generating_upper_and_one_lower_bound
    :
    UniformlyBoundedOn f S ∧ EquiLipschitzOn f S := by
  have hpointwise : PointwiseBoundedOn f C :=
    pointwiseBoundedOn_of_generating_upper_and_one_lower_bound f hf_convex hupper hlower
  simpa using
    hpointwise.uniformlyBoundedOn_and_equiLipschitzOn
      hC_ri hf_convex hS_compact hS_subset

omit hS_compact
/-- Closed/bounded bridge corollary of Theorem 10.6 (2). -/
theorem
    uniformlyBoundedOn_and_equiLipschitzOn_of_generating_upper_and_one_lower_bound_of_closed_bounded
    [ProperSpace E]
    (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) :
    UniformlyBoundedOn f S ∧ EquiLipschitzOn f S := by
  exact uniformlyBoundedOn_and_equiLipschitzOn_of_generating_upper_and_one_lower_bound
    (f := f) (C := C) (S := S)
    (hC_ri := hC_ri) (hf_convex := hf_convex)
    (hS_compact := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded)
    (hS_subset := hS_subset) (hupper := hupper) (hlower := hlower)

end GeneratingUpperAndOneLower

end
