import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_1_1

-- Declarations for this item will be appended below by the statement pipeline.

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
