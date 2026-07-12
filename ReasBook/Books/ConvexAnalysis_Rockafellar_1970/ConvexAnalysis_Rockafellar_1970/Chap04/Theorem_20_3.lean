import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 20.3 gives a closedness criterion for the Minkowski sum `C1 + C2` of a
  polyhedral convex set and a closed convex set under a one-sided recession-direction hypothesis.
- `core/canonical`: the left owner abstraction is `C1.IsFinitelyGeneratedConvex 𝕜`, because
  the closed-sum mechanism only uses finite generation, convexity, recession cones, lineality, and
  topological closure. The polyhedral hypothesis is a Chapter 19 bridge to that owner, not
  primitive data for the closedness statement itself.
- `bridge/view`: the source polyhedral statement is recovered from the core owner theorem through
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`. The textbook phrase “`z` is a direction
  in which `C2` is linear” is represented by `z ∈ lin[𝕜](C2)`, while the hypothesis that the
  opposite vector is a recession direction of `C2` is rendered by `-z ∈ 0⁺[𝕜] C2`.
  `Set.IsFinitelyGeneratedConvex.convex`, `Set.IsPolyhedral.isFinitelyGeneratedConvex`,
  the Chapter 2 owner theorems
  `LinearMap.closure_image_eq_image_closure_of_recessionKernelLeLineality`,
  `Set.ZeroSumRecessionImpLineality.isClosed_sum`, and the owners `0⁺[𝕜]` and
  `lin[𝕜](·)`.
- Primitive data vs derived API: the primitive inputs are the sets `C1`, `C2`, the finite-
  generation owner hypothesis on `C1`, the closed-convex hypotheses on `C2`, and the owner-level
  recession-versus-lineality condition. The closedness of the Minkowski sum is theorem-level
  content. The source polyhedral form is kept only as a thin bridge, and the textbook nonemptiness
  assumptions remain omitted because if either summand is empty then `C1 + C2 = ∅`, which is
  already closed.
- Ambient refinement: the core theorem uses no norm or inner-product data, and the sampled Chapter
  2 closure owners already live over finite-dimensional Hausdorff topological vector spaces over
  ordered complete normed fields. Its public owner level is therefore that weaker ambient layer
  rather than a real normed or inner-product specialization, or the concrete model
  `EuclideanSpace ℝ (Fin n)`.
-/

namespace Set.IsFinitelyGeneratedConvex

/-- Core owner companion to Theorem 20.3: if `C1` is a finitely generated convex set and `C2` is a
closed convex set in a finite-dimensional Hausdorff topological vector space over `𝕜`, and every
recession direction `z` of `C1` whose opposite `-z` is a recession direction of `C2` already
lies in the lineality space of `C2`, then the Minkowski sum `C1 + C2` is closed. -/
-- Proof sketch: replace `C1` by a finite mixed-hull presentation and apply the Chapter 2
-- closed-sum owner theorem for finitely many convex summands. The only nontrivial compatibility
-- condition needed there is the zero-sum recession-lineality hypothesis, and the finite-generation
-- presentation reduces that condition exactly to the displayed one-sided recession-lineality
-- condition for the left summand.
theorem isClosed_add_of_closed_of_opposite_recession_imp_lineality
    {C1 C2 : Set E} (hC1 : C1.IsFinitelyGeneratedConvex 𝕜) (hC2_conv : Convex 𝕜 C2)
    (hC2_closed : IsClosed C2)
    (hopposite_lineality :
      ∀ ⦃z : E⦄, z ∈ 0⁺[𝕜] C1 → -z ∈ 0⁺[𝕜] C2 → z ∈ lin[𝕜](C2)) :
    IsClosed (C1 + C2) := sorry

end Set.IsFinitelyGeneratedConvex

end

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Set.IsPolyhedral

/-- Theorem 20.3: if `C1` is a polyhedral convex set and `C2` is a
closed convex set in a finite-dimensional normed space over `𝕜`, and every
recession direction `z` of
`C1` whose opposite `-z` is a recession direction of `C2` already lies in the lineality space of
`C2`, then the Minkowski sum `C1 + C2` is closed. Specializing `𝕜 = ℝ` and
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem isClosed_add_of_closed_of_opposite_recession_imp_lineality
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜) (hC2_conv : Convex 𝕜 C2)
    (hC2_closed : IsClosed C2)
    (hopposite_lineality :
      ∀ ⦃z : E⦄, z ∈ 0⁺[𝕜] C1 → -z ∈ 0⁺[𝕜] C2 → z ∈ lin[𝕜](C2)) :
    IsClosed (C1 + C2) := sorry

end Set.IsPolyhedral

end
