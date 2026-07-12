import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open Bornology
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.8.2 says that if `Cᵢ` is a finite family of closed bounded convex
  sets, then the convex hull of their union is compact. The public Lean API keeps both
  source-facing surfaces: an explicit hull-closedness bridge and a stronger intrinsic theorem
  deriving hull-closedness from closedness/convexity/boundedness/nonemptiness of each component.
- `core/canonical`: this file's owner compactness theorem is
  `isCompact_closedConvexHull_of_isBounded_closedConvexHull`, whose primitive input is boundedness
  of the owner set `closedConvexHull ℝ S` itself. The source-facing boundedness transfer from `S`
  to the owner is a separate real-specific bridge (`isBounded_closedConvexHull_of_isBounded`),
  using the real convex-hull diameter API (`convexHull_diam` / `isBounded_convexHull`).
- `bridge/view`: closedness assumptions on `convexHull ℝ S` are treated as bridge data converting
  the source-facing hull to the canonical owner.

Domain-style sampling used here:
- `Metric.isCompact_of_isClosed_isBounded`;
- `closedConvexHull_eq_closure_convexHull`;
- `isBounded_biUnion_finset`.
- `isClosed_convexHull_iUnion_of_common_recessionCone`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.

Primitive data vs derived API:
- primitive input for owner compactness: `IsBounded (closedConvexHull ℝ S)`;
- real source-facing boundedness bridge input: `IsBounded S`;
- source-facing bridge input: `IsClosed (convexHull ℝ S)`;
- finite-operational bridge input: explicit closedness of the target hull together with
  `∀ i ∈ t, IsBounded (C i)`;
- source-facing bridge inputs:
  explicit `IsClosed (convexHull ℝ (⋃ i ∈ t, C i))`, with `[Finite ι]`-indexed `iUnion`
  as a derived corollary;
- source-facing intrinsic inputs: `[FiniteDimensional ℝ E]`, closedness/convexity/nonemptiness
  and boundedness of each family member;
- derived outputs: compactness of `closedConvexHull ℝ S` and, via bridge, compactness of
  `convexHull ℝ S`, including the intrinsic finite-family source statement.

Layer target: `bridge/view`; the primary theorem is a real-owner compactness theorem, and the
source-facing finite-family wrappers are retained as thin bridges.
-/

variable {C : ι → Set E} {S : Set E}

/-- Canonical owner compactness criterion for Corollary 9.8.2: in any proper pseudometric
additive `𝕜`-module, boundedness of `closedConvexHull 𝕜 S` implies compactness of
`closedConvexHull 𝕜 S`. -/
theorem isCompact_closedConvexHull_of_isBounded_closedConvexHull
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E' : Type*} [PseudoMetricSpace E'] [AddCommGroup E'] [Module 𝕜 E']
    [ProperSpace E']
    {S' : Set E'}
    (hHull_bounded : IsBounded (closedConvexHull 𝕜 S')) :
    IsCompact (closedConvexHull 𝕜 S') := by
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closedConvexHull hHull_bounded

/-- Real boundedness bridge for Corollary 9.8.2: boundedness of `S` implies boundedness of the
canonical owner `closedConvexHull ℝ S`. -/
theorem isBounded_closedConvexHull_of_isBounded
    (hS_bounded : IsBounded S) :
    IsBounded (closedConvexHull ℝ S) := by
  simpa [closedConvexHull_eq_closure_convexHull] using
    (isBounded_convexHull.2 hS_bounded).closure

/-- Real-owner compactness bridge for Corollary 9.8.2: in any proper real seminormed space,
boundedness of `S` implies compactness of `closedConvexHull ℝ S`. -/
theorem isCompact_closedConvexHull_of_isBounded
    [ProperSpace E]
    (hS_bounded : IsBounded S) :
    IsCompact (closedConvexHull ℝ S) := by
  exact isCompact_closedConvexHull_of_isBounded_closedConvexHull
    (isBounded_closedConvexHull_of_isBounded hS_bounded)

/-- Canonical hull-closed compactness bridge for Corollary 9.8.2: if `convexHull 𝕜 S` is closed
and `closedConvexHull 𝕜 S` is bounded, then `convexHull 𝕜 S` is compact. -/
-- Proof sketch: convert `convexHull 𝕜 S` to the canonical owner `closedConvexHull 𝕜 S` using
-- hull closedness, then apply owner compactness from bounded `closedConvexHull`.
theorem isCompact_convexHull_of_isClosedHull_of_isBounded_closedConvexHull
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {E' : Type*} [PseudoMetricSpace E'] [AddCommGroup E'] [Module 𝕜 E']
    [ProperSpace E']
    {S' : Set E'}
    (hHull_closed : IsClosed (convexHull 𝕜 S'))
    (hHull_bounded : IsBounded (closedConvexHull 𝕜 S')) :
    IsCompact (convexHull 𝕜 S') := by
  have hEq : closedConvexHull 𝕜 S' = convexHull 𝕜 S' := by
    apply Set.Subset.antisymm
    · exact closedConvexHull_min (subset_convexHull 𝕜 S') (convex_convexHull 𝕜 S') hHull_closed
    · exact convexHull_subset_closedConvexHull
  simpa [hEq] using
    (isCompact_closedConvexHull_of_isBounded_closedConvexHull
      (𝕜 := 𝕜) (S' := S') hHull_bounded)

/-- Source-facing compactness bridge for Corollary 9.8.2: in any proper real seminormed space,
if `convexHull ℝ S` is closed and `S` is bounded, then `convexHull ℝ S` is compact. -/
-- Proof sketch: transfer boundedness of `S` to boundedness of the canonical owner
-- `closedConvexHull ℝ S`, then apply the owner-primitive hull-closed compactness bridge.
theorem isCompact_convexHull_of_isClosedHull_of_isBounded
    [ProperSpace E]
    (hHull_closed : IsClosed (convexHull ℝ S))
    (hS_bounded : IsBounded S) :
    IsCompact (convexHull ℝ S) := by
  exact isCompact_convexHull_of_isClosedHull_of_isBounded_closedConvexHull
    hHull_closed
    (isBounded_closedConvexHull_of_isBounded hS_bounded)

/-- Corollary 9.8.2 9.8.2.1 (finite operational bridge): if the convex hull of a finite union is
known to be closed and the components are bounded, then that convex hull is compact. -/
-- Proof sketch: use `isBounded_biUnion_finset` to get boundedness of the finite union, then apply
-- the source-facing compactness bridge theorem.
theorem isCompact_convexHull_biUnion_finset_of_isClosedHull_of_isBounded
    [ProperSpace E]
    (t : Finset ι)
    (hHull_closed : IsClosed (convexHull ℝ (⋃ i ∈ t, C i)))
    (hC_bounded : ∀ i ∈ t, IsBounded (C i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ t, C i)) := by
  exact isCompact_convexHull_of_isClosedHull_of_isBounded
    hHull_closed
    ((isBounded_biUnion_finset t).2 hC_bounded)

section

variable [Finite ι]

/-- Corollary 9.8.2 9.8.2.1 (source-facing `iUnion` bridge): if the convex hull of a finite union
is closed and the components are bounded, then that convex hull is compact. -/
-- Proof sketch: instantiate the finite-operational theorem on `Finset.univ`.
theorem isCompact_convexHull_iUnion_of_isClosedHull_of_isBounded
    [ProperSpace E]
    (hHull_closed : IsClosed (convexHull ℝ (⋃ i, C i)))
    (hC_bounded : ∀ i, IsBounded (C i)) :
    IsCompact (convexHull ℝ (⋃ i, C i)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  simpa using
    (isCompact_convexHull_biUnion_finset_of_isClosedHull_of_isBounded
      (C := C) (t := (Finset.univ : Finset ι))
      (by simpa using hHull_closed)
      (fun i _ => hC_bounded i))

/-- Scalar-generic closedness bridge behind Corollary 9.8.2: in finite dimension, if each `C i`
is closed, convex, nonempty, and bounded, then the convex hull of their union is closed. -/
theorem isClosed_convexHull_iUnion_of_isClosed_of_convex_of_isBounded
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
    [LocallyCompactSpace 𝕜]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [FiniteDimensional 𝕜 E']
    {C : ι → Set E'}
    (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex 𝕜 (C i))
    (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_bounded : ∀ i, IsBounded (C i)) :
    IsClosed (convexHull 𝕜 (⋃ i, C i)) := by
  haveI : ProperSpace E' := FiniteDimensional.proper 𝕜 E'
  have hK : ∀ i, 0⁺[𝕜] (C i) = ({0} : Set E') := by
    intro i
    exact ((hC_convex i).isBounded_iff_recessionCone_eq_singleton_zero
      (hC_closed i) (hC_nonempty i)).1 (hC_bounded i)
  exact isClosed_convexHull_iUnion_of_common_recessionCone
    ({0} : Set E') hC_closed hC_convex hK

/-- Corollary 9.8.2 (intrinsic finite-family surface): in finite dimension, if each `C i` is
closed, convex, nonempty, and bounded, then the convex hull of their union is compact. -/
-- Proof sketch: first use the scalar-generic closedness bridge to prove
-- `IsClosed (convexHull ℝ (⋃ i, C i))`, then boundedness of `⋃ i, C i` and the real compactness
-- bridge `isCompact_convexHull_of_isClosedHull_of_isBounded`.
theorem isCompact_convexHull_iUnion_of_isClosed_of_convex_of_isBounded
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {C' : ι → Set E'}
    (hC_closed : ∀ i, IsClosed (C' i))
    (hC_convex : ∀ i, Convex ℝ (C' i))
    (hC_nonempty : ∀ i, (C' i).Nonempty)
    (hC_bounded : ∀ i, IsBounded (C' i)) :
    IsCompact (convexHull ℝ (⋃ i, C' i)) := by
  have hHull_closed : IsClosed (convexHull ℝ (⋃ i, C' i)) :=
    isClosed_convexHull_iUnion_of_isClosed_of_convex_of_isBounded
      hC_closed hC_convex hC_nonempty hC_bounded
  have hUnion_bounded : IsBounded (⋃ i, C' i) := (isBounded_iUnion).2 hC_bounded
  haveI : ProperSpace E' := FiniteDimensional.proper ℝ E'
  exact isCompact_convexHull_of_isClosedHull_of_isBounded hHull_closed hUnion_bounded

end

end
