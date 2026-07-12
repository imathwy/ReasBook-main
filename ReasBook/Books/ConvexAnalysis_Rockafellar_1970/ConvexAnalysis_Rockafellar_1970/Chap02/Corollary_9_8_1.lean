import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_8

-- Declarations for this item will be appended below by the statement pipeline.

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
