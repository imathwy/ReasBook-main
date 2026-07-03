import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_9_8_1 (from Chap02) -/
section

universe u

variable {ι : Type u}
variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

open scoped BigOperators Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.8.1 states that if finitely many closed convex sets share the same
  recession cone `K`, then the convex hull of their union is closed and has recession cone `K`.
  The public Lean statement below keeps this on the intrinsic chapter ambient layer of
  Hausdorff topological vector spaces over `𝕜` with the owner-level finite-dimensional hypothesis
  on the ambient space `E`.
  The common-cone hypothesis `0⁺[𝕜] (C i) = K` makes the source nonemptiness
  assumption redundant, so the bridge exposes only the mathematically active hypotheses.
  The finite family is kept at the canonical `C : ι → Set E` / `[Finite ι]` layer.
- `core/canonical`: the owner result is Theorem 9.8, namely
  `closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination` together with
  `recessionCone_closedConvexHull_iUnion_eq_finset_sum_recessionCone`, built on the chapter
  owner `recessionCone` with source notation `0⁺[𝕜]`, and the canonical owner
  `closedConvexHull 𝕜`.
- `bridge/view`: this file is the thin specialization from the owner hypothesis in Theorem 9.8
  (zero-sum recession directions lie in the corresponding lineality spaces) to the intrinsic
  pairwise hypothesis
  `Pairwise (fun i j => 0⁺[𝕜] (C i) = 0⁺[𝕜] (C j))`, then to the source-visible
  common-cone hypothesis `0⁺[𝕜] (C i) = K`. Rockafellar's list `C₁, ..., C_m` is rendered as a
  finite family `C : ι → Set E`; the common-cone implication is factored into one private theorem
  rather than duplicated across both corollaries.
  Only the recession-cone clause keeps `[Nonempty ι]`,
  because the owner recession formula from Theorem 9.8 needs a nonempty index type while the
  closedness clause remains valid for the empty family.
- Domain-style sampling: the relevant owner-side declarations here are `recessionCone`,
  `Set.linealitySpace`,
  `closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination`, and
  `recessionCone_closedConvexHull_iUnion_eq_finset_sum_recessionCone`, together with the ambient
  chapter style already used in `Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure`
  and
  `Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure`.
- Primitive data vs derived API: the primitive owner input is the family-level compatibility
  condition `C ⟂Σ₀⁺[𝕜]` from Corollary 9.1.1, together with closedness and convexity of each
  `C i`. The pairwise and common-cone hypotheses are bridge layers above that owner surface.
  The source nonemptiness assumption is derived internally in the nontrivial branch where
  Theorem 9.8 is invoked, while the empty-set branch collapses to the canonical `∅`/`univ`
  cases. The closedness of `convexHull 𝕜 (⋃ i, C i)` and the recession-cone identity are first
  exposed on the owner layer `C ⟂Σ₀⁺[𝕜]`, then bridged to pairwise and source-visible `= K`
  surfaces.
- Layer target: `bridge/view`; the public corollaries remain source-facing, but the abstraction
  boundary is the owner theorem from Theorem 9.8 rather than a parallel local family package.
- Ambient minimization: the public statements use only owner-level notions `IsClosed`, `Convex`,
  `convexHull 𝕜`, and `0⁺[𝕜]`, matching the surrounding Chapter 2 owner API.
-/

variable {C : ι → Set E}

private theorem pairwise_recessionCone_imp_zeroSumRecessionImpLineality [Fintype ι]
    (hpair : Pairwise fun i j : ι => 0⁺[𝕜] (C i) = 0⁺[𝕜] (C j)) :
    C ⟂Σ₀⁺[𝕜] := by
  sorry

section

variable [Finite ι]

/-- Canonical-owner form of Corollary 9.8.1 (1), using `C ⟂Σ₀⁺[𝕜]`. -/
theorem convexHull_iUnion_eq_closedConvexHull_iUnion_of_zeroSumRecessionImpLineality
    [Fintype ι]
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hzero : C ⟂Σ₀⁺[𝕜]) :
    convexHull 𝕜 (⋃ i, C i) = closedConvexHull 𝕜 (⋃ i, C i) := by
  sorry

/-- Intrinsic pairwise-equality bridge form of Corollary 9.8.1 (1). -/
theorem convexHull_iUnion_eq_closedConvexHull_iUnion_of_pairwise_recessionCone
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hpair : Pairwise fun i j : ι => 0⁺[𝕜] (C i) = 0⁺[𝕜] (C j)) :
    convexHull 𝕜 (⋃ i, C i) = closedConvexHull 𝕜 (⋃ i, C i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact convexHull_iUnion_eq_closedConvexHull_iUnion_of_zeroSumRecessionImpLineality
    hclosed hconv
    (pairwise_recessionCone_imp_zeroSumRecessionImpLineality hpair)

/-- Source-facing `= K` bridge for Corollary 9.8.1 (1). -/
theorem convexHull_iUnion_eq_closedConvexHull_iUnion_of_common_recessionCone
    (K : Set E)
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hK : ∀ i, 0⁺[𝕜] (C i) = K) :
    convexHull 𝕜 (⋃ i, C i) = closedConvexHull 𝕜 (⋃ i, C i) := by
  apply convexHull_iUnion_eq_closedConvexHull_iUnion_of_pairwise_recessionCone hclosed hconv
  intro i j _
  simp [hK i, hK j]

/-- Canonical-owner closedness form of Corollary 9.8.1 (1), using `C ⟂Σ₀⁺[𝕜]`. -/
theorem isClosed_convexHull_iUnion_of_zeroSumRecessionImpLineality
    [Fintype ι]
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hzero : C ⟂Σ₀⁺[𝕜]) :
    IsClosed (convexHull 𝕜 (⋃ i, C i)) := by
  have hHull :
      convexHull 𝕜 (⋃ i, C i) = closedConvexHull 𝕜 (⋃ i, C i) :=
    convexHull_iUnion_eq_closedConvexHull_iUnion_of_zeroSumRecessionImpLineality
      hclosed hconv hzero
  have hClosed : IsClosed (closedConvexHull 𝕜 (⋃ i, C i)) :=
    isClosed_closedConvexHull
  simpa [hHull] using hClosed

/-- Intrinsic pairwise-equality form of Corollary 9.8.1 (1), stated as closedness. -/
theorem isClosed_convexHull_iUnion_of_pairwise_recessionCone
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hpair : Pairwise fun i j : ι => 0⁺[𝕜] (C i) = 0⁺[𝕜] (C j)) :
    IsClosed (convexHull 𝕜 (⋃ i, C i)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact isClosed_convexHull_iUnion_of_zeroSumRecessionImpLineality
    hclosed hconv
    (pairwise_recessionCone_imp_zeroSumRecessionImpLineality hpair)

/-- Corollary 9.8.1 (1): if finitely many closed convex subsets of a Hausdorff topological vector
space over `𝕜` share a common recession cone `K`, and the chapter ambient finite-dimensionality
condition on `E` holds, then the convex hull of
their union is closed. -/
-- Proof sketch: if every `C i` is nonempty, then under the common-cone hypothesis any zero-sum
-- family of recession directions belongs termwise to the corresponding lineality spaces, so
-- Theorem 9.8 upgrades the source-facing common-cone hypothesis to the owner-level closed-convex-
-- hull description. That identifies `convexHull 𝕜 (⋃ i, C i)` with the canonical owner
-- `closedConvexHull 𝕜 (⋃ i, C i)`, whose closedness is built in.
-- If some `C i` is empty, then `0⁺[𝕜] (C i) = univ`, hence `K = univ`, so every `C j` is either
-- `∅` or `univ`; the union and its convex hull are therefore canonically `∅` or `univ`, both
-- closed.
theorem isClosed_convexHull_iUnion_of_common_recessionCone
    (K : Set E)
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hK : ∀ i, 0⁺[𝕜] (C i) = K) :
    IsClosed (convexHull 𝕜 (⋃ i, C i)) := by
  apply isClosed_convexHull_iUnion_of_pairwise_recessionCone hclosed hconv
  intro i j _
  simp [hK i, hK j]

section

/-- Canonical-owner form of Corollary 9.8.1 (2), using `C ⟂Σ₀⁺[𝕜]`. -/
theorem recessionCone_convexHull_iUnion_eq_recessionCone_of_zeroSumRecessionImpLineality
    [Fintype ι] (i : ι)
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hzero : C ⟂Σ₀⁺[𝕜]) :
    0⁺[𝕜] (convexHull 𝕜 (⋃ i, C i)) = 0⁺[𝕜] (C i) := by
  sorry

/-- Intrinsic pairwise-equality form of Corollary 9.8.1 (2). -/
theorem recessionCone_convexHull_iUnion_eq_recessionCone (i : ι)
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hpair : Pairwise fun j k : ι => 0⁺[𝕜] (C j) = 0⁺[𝕜] (C k)) :
    0⁺[𝕜] (convexHull 𝕜 (⋃ i, C i)) = 0⁺[𝕜] (C i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact recessionCone_convexHull_iUnion_eq_recessionCone_of_zeroSumRecessionImpLineality
    i hclosed hconv
    (pairwise_recessionCone_imp_zeroSumRecessionImpLineality hpair)

variable [Nonempty ι]

/-- Corollary 9.8.1 (2): under the same hypotheses, the recession cone of the convex hull of the
union is exactly the common recession cone `K`. -/
-- Proof sketch: Theorem 9.8 identifies the recession cone of
-- `closedConvexHull 𝕜 (⋃ i, C i)` with the finite sum of the individual recession cones. Under
-- the common-cone hypothesis this sum collapses to `K`, and the bridge
-- `convexHull 𝕜 (⋃ i, C i) = closedConvexHull 𝕜 (⋃ i, C i)` removes the closed owner from the
-- recession-cone argument in the nonempty branch.
-- If some `C i` is empty, then `K = univ` and the convex hull of the union is `∅` or `univ`,
-- both with recession cone `univ`.
theorem recessionCone_convexHull_iUnion_eq_common_recessionCone
    (K : Set E)
    (hclosed : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hK : ∀ i, 0⁺[𝕜] (C i) = K) :
    0⁺[𝕜] (convexHull 𝕜 (⋃ i, C i)) = K := by
  let i : ι := Classical.choice ‹Nonempty ι›
  calc
    0⁺[𝕜] (convexHull 𝕜 (⋃ i, C i)) = 0⁺[𝕜] (C i) :=
      recessionCone_convexHull_iUnion_eq_recessionCone i hclosed hconv
        (by
          intro j k _
          simp [hK j, hK k])
    _ = K := hK i

end

end

end

/-! ### Corollary_9_8_2_9_8_2_1 (from Chap02) -/
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

/-! ### Corollary_9_8_3_9_8_3_1 (from Chap02) -/
open scoped BigOperators Rockafellar

noncomputable section

section

variable {ι : Type*} [Finite ι]
variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 9.8.3.1 says that if finitely many closed proper convex functions on
  a finite-dimensional Hausdorff topological vector space over `𝕜` have the same recession
  function,
  then their convex hull is again closed and proper, has that same recession function, and the
  finite-convex-combination infimum formula from Theorem 5.6 is attained at every point.
- `core/canonical`: the existing owner objects are `Function.convexHull`, used here through the
  source-facing specialization `conv(⨅ i, f i)` for the convex hull of a family of functions,
  `LowerSemicontinuous` for closedness, `f.IsProper` for properness, and
  `Function.recessionFunction` for recession functions.
- `bridge/view`: Rockafellar's list `f₁, ..., f_m` is represented by a family
  `f : ι → E → WithTopBot 𝕜`, and the attainment clause uses the canonical finite-simplex owners
  packaged in `Function.convexCombinationValues`, whose point and value coordinates are both
  expressed through the canonical `StdSimplex.sum` interface from Theorem 5.6.

Domain-style sampling used here:
- `Function.convexHull_iInf_eq_verticalInfimum_convexHull_iUnion_epigraph`;
- `Function.convexHull_iInf_eq_sInf_convexCombination_values`;
- `Function.convexCombinationValues`;
- `StdSimplex.sum`;
- `Function.recessionFunction`;
- `recessionCone_convexHull_iUnion_eq_common_recessionCone`.

Primitive data vs derived API:
- primitive inputs for the owner-side epigraph consequences: the family `f`, the intrinsic common-
  recession-function owner hypothesis `∃ g, ∀ i, (f i)₀⁺ = g` (with pairwise equality used as a
  bridge form), and the convexity and lower-semicontinuity hypotheses on each `f i`;
- extra primitive input for the owner bridge from epigraph recession cones back to recession
  functions, and hence for the closedness, properness, recession-function, and attainment clauses:
  properness of each `f i`;
- extra primitive input for the nontrivial properness and attainment clauses: `Nonempty ι`, which
  rules out the empty-family degeneracy;
- derived conclusions: lower semicontinuity, properness, preservation of the common recession
  function, and attainment for the already-canonical finite-convex-combination formula
  `Function.convexHull_iInf_eq_sInf_convexCombination_values`, expressed on the canonical owner
  `Function.convexCombinationValues`.

Ambient minimization check:
- unlike the family convex-hull owner from Theorem 5.6, the closedness and common-recession
  consequences here are obtained by passing to scalar epigraphs and invoking Corollary 9.8.1;
- since that owner theorem already lives on the intrinsic chapter ambient of finite-dimensional
  Hausdorff topological vector spaces over `𝕜`, this file should reuse the same ambient layer
  rather than falling back to the coordinate model `R^n = EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`; the item is stated directly for the textbook convex hull
`conv {f_i | i ∈ ι}` as the canonical owner `conv(⨅ i, f i)`, without introducing any extra
package or wrapper around the family. The primitive public common-recession assumption is the
intrinsic existence form `∃ g, ∀ i, (f i)₀⁺ = g`; pairwise equalities are retained as thin bridges,
and the explicit-value form is kept where the conclusion itself names the common function `g`.
-/

variable {f : ι → E → WithTopBot 𝕜}

private theorem lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    LowerSemicontinuous (conv(⨅ i, f i)) := sorry

/-- Corollary 9.8.3.1 (1), source-facing common-recession form: if a finite family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a common
recession function, then its convex hull is closed, expressed here by lower semicontinuity. -/
-- Proof sketch: apply Corollary 9.8.1 to the scalar epigraphs of the functions `f i`. Closedness
-- and convexity of those epigraphs come from `hf_closed` and `hf_convex`, while the common
-- recession-function hypothesis identifies those recession cones pairwise. Properness is used to
-- identify each epigraph recession cone with the epigraph of `(f i)₀⁺`. Reading the resulting
-- closed convex hull back as an epigraph gives lower semicontinuity of `conv(⨅ i, f i)`.
theorem lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    LowerSemicontinuous (conv(⨅ i, f i)) := by
  rcases h_common_recession with ⟨_, hg⟩
  exact lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (1), intrinsic bridge form: if a finite family of closed proper convex
functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise equal
recession functions, then its convex hull is closed. -/
theorem lowerSemicontinuous_convexHull_iInf_of_pairwise_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    LowerSemicontinuous (conv(⨅ i, f i)) := by
  exact lowerSemicontinuous_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

section

variable [Nonempty ι]

private theorem isProper_convexHull_iInf_of_common_recessionFunction_core
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    (conv(⨅ i, f i)).IsProper := sorry

/-- Corollary 9.8.3.1 (2), source-facing common-recession form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function, then its convex hull is proper. -/
-- Proof sketch: the epigraph of `conv(⨅ i, f i)` is the closed convex hull of the
-- union of the epigraphs of the `f i`. Part (1) gives lower semicontinuity, while
-- the owner theorem `Function.isGreatest_conv_iInf_minorant` supplies convexity of
-- `conv(⨅ i, f i)`. Properness then amounts to excluding the degenerate values `⊥` and `⊤`,
-- which follows from the properness of each `f i` together with the common recession-function
-- hypothesis.
theorem isProper_convexHull_iInf_of_common_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    (conv(⨅ i, f i)).IsProper := by
  rcases h_common_recession with ⟨_, hg⟩
  exact isProper_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (2), intrinsic bridge form: if a finite nonempty family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise
equal recession functions, then its convex hull is proper. -/
theorem isProper_convexHull_iInf_of_pairwise_recessionFunction
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    (conv(⨅ i, f i)).IsProper := by
  exact isProper_convexHull_iInf_of_common_recessionFunction_core
    hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

end

private theorem recessionFunction_convexHull_iInf_eq_common_core (i : ι)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ := sorry

section

variable [Nonempty ι]

/-- Corollary 9.8.3.1 (3), source-facing common-value form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function `g`, then the recession function of its convex hull agrees with `g`. -/
-- Proof sketch: pass to scalar epigraphs and apply Corollary 9.8.1 to identify the recession
-- cone of the convex hull of their union with the common recession cone of the family epigraphs.
-- Properness identifies those epigraph recession cones with the epigraphs of the recession
-- functions. The convex hull epigraph is exactly the epigraph of `conv(⨅ i, f i)`, so comparing
-- those epigraph recession cones gives the stated equality of recession functions.
theorem recessionFunction_convexHull_iInf_eq_common_recessionFunction
    (g : E → WithTopBot 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ j, (f j)₀⁺ = g) :
    (conv(⨅ i, f i))₀⁺ = g := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  calc
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ :=
      recessionFunction_convexHull_iInf_eq_common_core i
        hf_convex hf_closed hf_proper
        (by
          intro j k
          simp [h_common_recession j, h_common_recession k])
    _ = g := h_common_recession i

end

/-- Corollary 9.8.3.1 (3), intrinsic bridge form: if a finite family of closed proper convex
functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise equal
recession functions, then the recession function of its convex hull agrees with `(f i)₀⁺` for any
chosen index `i`. -/
theorem recessionFunction_convexHull_iInf_eq_recessionFunction_of_pairwise (i : ι)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    (conv(⨅ i, f i))₀⁺ = (f i)₀⁺ := by
  exact recessionFunction_convexHull_iInf_eq_common_core i
    hf_convex hf_closed hf_proper
    (by
      intro j k
      by_cases hjk : j = k
      · simp [hjk]
      · exact h_pairwise_recession hjk)

section

variable [Nonempty ι]

private theorem exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∀ i j, (f i)₀⁺ = (f j)₀⁺) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := sorry

/-- Corollary 9.8.3.1 (4), source-facing common-recession form: if a finite nonempty family of closed
proper convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has a
common recession function, then for each `x` the infimum in
`Function.convexHull_iInf_eq_sInf_convexCombination_values` is attained, equivalently by
membership of `conv(⨅ i, f i) x` in the canonical owner
`Function.convexCombinationValues (⨅ i, f i) x`. -/
-- Proof sketch: `Function.convexHull_iInf_eq_sInf_convexCombination_values` identifies
-- `conv(⨅ i, f i) x` with the infimum over finite convex combinations of function
-- values. Since part (1) gives closedness and part (3) identifies the common recession function
-- of the resulting epigraph, the closed convex hull of the union of the epigraphs contains the
-- point `(x, conv(⨅ i, f i) x)` itself. Unwinding the proof of Theorem 5.6, that
-- point comes from one finite convex combination, which exactly says that
-- `conv(⨅ i, f i) x` belongs to `Function.convexCombinationValues (⨅ i, f i) x`.
theorem exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_common_recession : ∃ g, ∀ i, (f i)₀⁺ = g) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := by
  rcases h_common_recession with ⟨_, hg⟩
  exact exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    x hf_convex hf_closed hf_proper
    (by
      intro i j
      simp [hg i, hg j])

/-- Corollary 9.8.3.1 (4), intrinsic bridge form: if a finite nonempty family of closed proper
convex functions on a finite-dimensional Hausdorff topological vector space over `𝕜` has pairwise
equal recession functions, then for each `x` the infimum in
`Function.convexHull_iInf_eq_sInf_convexCombination_values` is attained. -/
theorem exists_finite_convex_combination_eq_convexHull_iInf_of_pairwise_recessionFunction
    (x : E)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_recession : Pairwise (fun i j : ι => (f i)₀⁺ = (f j)₀⁺)) :
    conv(⨅ i, f i) x ∈ Function.convexCombinationValues (⨅ i, f i) x := by
  exact exists_finite_convex_combination_eq_convexHull_iInf_of_common_recessionFunction_core
    x hf_convex hf_closed hf_proper
    (by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact h_pairwise_recession hij)

end

end

end

/-! ### Theorem_9_8 (from Chap02) -/
open scoped BigOperators Pointwise Rockafellar

section

universe u

variable {ι : Type u} [Fintype ι]
variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 9.8 describes the closure of the convex hull of finitely many nonempty
  convex sets under Rockafellar's zero-sum recession-direction hypothesis, together with
  the recession cone of that closure.
- `core/canonical`: the owner notions are `closedConvexHull 𝕜`, the chapter owner
  `recessionCone`, the chapter owner `Set.lineal`, the simplex owner
  `StdSimplex 𝕜 ι` for the coefficients, the family-compatibility owner
  `Set.ZeroSumRecessionImpLineality 𝕜 C`, and the finite pointwise set sum `∑ i, S i`.
- `bridge/view`: the textbook convention `λᵢ ≥ 0⁺` is expressed directly by replacing the summand
  `λᵢ • cl(Cᵢ)` with `0⁺[𝕜] (cl(Cᵢ))` exactly when `w.weights i = 0`; no parallel coefficient
  package is introduced. The public owner theorem is stated directly as a set-of-membership
  equality with a simplex witness, and a companion indexed-union theorem is kept only as
  display-level bridge.
- Domain-style sampling used here: `StdSimplex 𝕜 ι`, the chapter owners `recessionCone` and
  `Set.lineal`, the canonical owner `closedConvexHull 𝕜`, the finite-family owner lemmas
  `Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure` and
  `Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure`,
  and the convex-hull owner `convexHull 𝕜`.
- Primitive data vs derived API: the primitive inputs are the family `C`, convexity and
  nonemptiness of each `C i`, and the zero-sum recession-lineality hypothesis on the closure
  layer. The owner equality for `closedConvexHull 𝕜 (⋃ i, C i)` and the recession-cone formula for
  that owner are the two derived conclusions, so they are exposed as separate atomic theorems.
  The owner equality remains meaningful for empty index types, while the recession-cone formula
  needs the extra nonempty-index hypothesis because
  `0⁺[𝕜] (closedConvexHull 𝕜 (⋃ i, C i)) = univ` but the empty finite sum is `{0}`.
- Layer target: this item remains `source-facing`, stated directly in terms of the convex hull of
  the union rather than through a new family wrapper.
- Ambient refinement: this theorem is source-facing on the intrinsic finite-dimensional ambient
  space `E`, while the tuple-space finite-dimensional assumptions needed by Chapter 9 transport
  lemmas remain internal bridge machinery.
- Scalar/ambient minimization audit:
  `Field 𝕜`, `LinearOrder 𝕜`, `TopologicalSpace 𝕜`, `OrderTopology 𝕜`, and
  `IsStrictOrderedRing 𝕜` are retained exactly because the reused Chapter 9 transport owners
  `Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure` and
  `Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure`
  currently live on that scalar layer; no weaker upstream owner bridge is available here.
- Topology-language audit: this item keeps ambient `closure`/`closedConvexHull`/`recessionCone`
  phrasing because the source object is a subset of the ambient space `E` itself and no
  distinguished carrier subset is part of the primitive data; a relative-topology reformulation
  would introduce extra non-primitive parameters.
-/

variable {C : ι → Set E}

/-- Theorem 9.8 (1): if `C₁, ..., C_m` are nonempty convex subsets such that every
zero-sum tuple of recession directions lies termwise in the corresponding lineality spaces on the
closure layer, then the closed convex hull of their union is exactly the set of points belonging
to a simplex combination in which a zero coefficient contributes the recession cone of the
corresponding closure. -/
-- Proof sketch: combine the Chapter 9 finite-family closure/recession transport for sums under
-- `Set.ZeroSumRecessionImpLineality` with the simplex-weight decomposition of convex hull points,
-- then rewrite the source decomposition directly on the owner
-- `closedConvexHull 𝕜 (⋃ i, C i)`.
theorem closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hzero : C ⟂Σ₀⁺[𝕜])
    :
    closedConvexHull 𝕜 (⋃ i, C i) =
      ({x : E |
        ∃ w : StdSimplex 𝕜 ι,
          x ∈ ∑ i,
            (if w.weights i = 0 then 0⁺[𝕜] (closure (C i))
             else w.weights i • closure (C i) : Set E)} : Set E) := sorry

/-- Theorem 9.8 (1), display form: the owner equality above rewritten as an indexed union over
simplex weights. -/
theorem closedConvexHull_iUnion_eq_iUnion_simplex_recession_combination
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hzero : C ⟂Σ₀⁺[𝕜])
    :
    closedConvexHull 𝕜 (⋃ i, C i) =
      ⋃ w : StdSimplex 𝕜 ι,
        ∑ i,
          (if w.weights i = 0 then 0⁺[𝕜] (closure (C i))
           else w.weights i • closure (C i) : Set E) := by
  ext x
  rw [closedConvexHull_iUnion_eq_setOf_mem_simplex_recession_combination
    (hconv := hconv) (hne := hne) (hzero := hzero)]
  simp

section

variable [Nonempty ι]

/-- Theorem 9.8 (2): if moreover the index type is nonempty, then the recession cone of the closed
convex hull of the
union is the finite sum of the recession cones of the individual closures. -/
-- Proof sketch: after part (1), apply the Chapter 9 recession formula for finite sums under the
-- same zero-sum lineality hypothesis, and use `[Nonempty ι]` to avoid the degenerate empty-index
-- discrepancy between `0⁺[𝕜] (closedConvexHull 𝕜 (⋃ i, C i))` and an empty finite sum.
theorem recessionCone_closedConvexHull_iUnion_eq_finset_sum_recessionCone
    (hconv : ∀ i, Convex 𝕜 (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hzero : C ⟂Σ₀⁺[𝕜])
    :
    0⁺[𝕜] (closedConvexHull 𝕜 (⋃ i, C i)) = ∑ i, 0⁺[𝕜] (closure (C i)) := sorry

end

end
