import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise Rockafellar

section

universe u

variable {ι : Type u} [Fintype ι]

variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.1.3 specializes the finite-sum closure criterion to a finite family
  of nonempty convex cones, replacing the recession-direction hypothesis by the source-visible
  stronger condition that the zero-sum tuple already lies in the closures of the cones.
- `core/canonical`: the owner abstractions are mathlib's bundled `PointedCone 𝕜 E` (the intrinsic
  owner for nonempty cones), the chapter owner `Set.linealitySpace`, topological closure, and
  finite pointwise set sums.
- `bridge/view`: the result is a direct specialization of Corollary 9.1.1 to cone carriers; no new
  cone wrapper is introduced. The source hypothesis is kept as the direct zero-sum closure
  condition on cone families.
- Domain-style sampling used here: `PointedCone 𝕜 E`,
  `Set.linealitySpace`, `Set.mem_recessionCone_iff`,
  `Set.ZeroSumRecessionImpLineality`, and
  `Set.ZeroSumRecessionImpLineality.closure_sum_eq_sum_closure`.
- Primitive data vs derived API: the primitive inputs are the cone family `K` and the zero-sum
  condition on points of the closures. The finite-sum owner theorem already absorbs empty
  summands, so familywise nonemptiness is not primitive public data here. The closure identity for
  the finite Minkowski sum is the derived statement.
- Layer target: this item stays `source-facing`, but uses the canonical bundled cone owner for the
  summands and the same intrinsic finite-family ambient layer as Corollary 9.1.1 rather than the
  coordinate model `EuclideanSpace ℝ (Fin n)`.
--/

namespace PointedCone

-- Bridge from the source closure-level tuple condition to Corollary 9.1.1's canonical owner
-- condition on zero-sum recession directions of closure summands.
omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] in
theorem zeroSumRecessionImpLineality_of_zero_sum_closure_imp_lineality
    (K : ι → PointedCone 𝕜 E)
    (hzero :
      ∀ z : ι → E,
        (∀ i, z i ∈ closure (K i : Set E)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ lin[𝕜](closure (K i : Set E))) :
    Set.ZeroSumRecessionImpLineality 𝕜 (fun i ↦ (K i : Set E)) := by
  intro z hz hsum i
  apply hzero z ?_ hsum i
  intro j
  have hzero_mem : (0 : E) ∈ closure (K j : Set E) := subset_closure (K j).zero_mem
  simpa using (Set.mem_recessionCone_iff.mp (hz j)) 0 hzero_mem (1 : 𝕜) zero_le_one

/-- Cone-specialized canonical-owner form of Corollary 9.1.1 (1):
under `⟂Σ₀⁺[𝕜]` for cone carriers, closure commutes with finite Minkowski sums. -/
theorem closure_sum_eq_sum_closure
    (K : ι → PointedCone 𝕜 E)
    (hzero : Set.ZeroSumRecessionImpLineality 𝕜 (fun i ↦ (K i : Set E))) :
    closure (∑ i, (K i : Set E)) = ∑ i, closure (K i : Set E) := by
  exact hzero.closure_sum_eq_sum_closure (fun i ↦ (K i).convex)

end PointedCone

-- Proof sketch: first convert the source closure-level tuple condition into the canonical
-- zero-sum recession owner condition on cone carriers; then apply the cone-specialized
-- canonical-owner closure theorem above.
/-- Corollary 9.1.3: for nonempty convex cones `K₁, …, K_m` in `R^n`, if every zero-sum tuple
`zᵢ ∈ cl Kᵢ` lies termwise in the lineality spaces of the closures, then the closure of the finite
Minkowski sum equals the finite sum of the individual closures. -/
theorem closure_sum_eq_sum_closure_of_zero_sum_closure_imp_lineality
    (K : ι → PointedCone 𝕜 E)
    (hzero :
      ∀ z : ι → E,
        (∀ i, z i ∈ closure (K i : Set E)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ lin[𝕜](closure (K i : Set E))) :
    closure (∑ i, (K i : Set E)) = ∑ i, closure (K i : Set E) := by
  exact PointedCone.closure_sum_eq_sum_closure
    K (PointedCone.zeroSumRecessionImpLineality_of_zero_sum_closure_imp_lineality K hzero)

end
