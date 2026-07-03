import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_20_3_1 (from Chap04) -/
section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 20.3.1 asserts strong hyperplane separation for a disjoint nonempty
  polyhedral convex set `C1` and nonempty closed convex set `C2` under the common-recession-
  versus-lineality hypothesis that makes `C1 - C2` closed.
- `core/canonical`: the owner abstractions are `Set.IsPolyhedral`, `0⁺[𝕜]`, `lin[𝕜](·)`, the
  pointwise difference set `C1 - C2`, and the Chapter 11 owner relation
  `AffineSubspace.StronglySeparates`.
- `bridge/view`: the source common-recession condition is
  `z ∈ 0⁺[𝕜] C1 → z ∈ 0⁺[𝕜] C2 → z ∈ lin[𝕜](C2)`; the proof bridges
  this to Theorem 20.3 by replacing `C2` with `-C2`.
- Domain-style sampling used here: the project declarations
  `Set.IsPolyhedral.isClosed_add_of_closed_of_opposite_recession_imp_lineality`,
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`,
  `AffineSubspace.StronglySeparates`,
  `exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub`, `0⁺[𝕜]`,
  `lin[𝕜](·)`, and
  `Set.neg_mem_recessionCone_neg_iff`.
- Primitive data vs derived API: the primitive inputs are the two sets, their polyhedrality,
  convexity, closedness, nonemptiness, disjointness, and the recession-lineality hypothesis.
  Existence of a strongly separating hyperplane is theorem-level output, so the file uses the
  existing owner `AffineSubspace.StronglySeparates` directly rather than a parallel `(b, β)`
  witness package.
- Layer target: `source-facing`, stated directly with the Chapter 11 strong-separation owner.
- Ambient refinement: the proof uses only the Chapter 20 closed-sum owner and the Chapter 11
  separation owner, both already formulated on finite-dimensional normed pairing spaces over an
  ordered complete normed field. The corollary therefore lives canonically on that common owner
  layer rather than the concrete model `EuclideanSpace ℝ (Fin n)`.
-/

/-- Corollary 20.3.1: if `C1` is a nonempty polyhedral convex set and `C2` is a nonempty closed
convex set in a finite-dimensional normed pairing space over an ordered complete normed field
`𝕜`, if `C1` and `C2` are disjoint, and
if every common recession direction of `C1` and `C2` already lies in the lineality space of `C2`,
then some hyperplane strongly separates `C1` and `C2`. Specializing `𝕜 = ℝ` and
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
-- Proof sketch: apply Theorem 20.3 to `C1` and `-C2`; the common-recession hypothesis becomes
-- the needed opposite-recession hypothesis after negating `C2`, so `C1 - C2 = C1 + (-C2)` is
-- closed. Since `C1` and `C2` are disjoint, `(0 : E) ∉ C1 - C2`, hence also
-- `(0 : E) ∉ closure (C1 - C2)`. The Chapter 11 strong-separation criterion then yields a
-- hyperplane strongly separating `C1` and `C2`.
theorem exists_hyperplane_strongly_separating_of_disjoint_of_common_recession_imp_lineality
    {C1 C2 : Set E} (hC1_poly : C1.IsPolyhedral 𝕜) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) (hC2_closed : IsClosed C2)
    (hdisj : Disjoint C1 C2)
    (hcommon_lineality :
      ∀ ⦃z : E⦄, z ∈ 0⁺[𝕜] C1 → z ∈ 0⁺[𝕜] C2 → z ∈ lin[𝕜](C2)) :
    ∃ H : AffineSubspace 𝕜 E, H.StronglySeparates (Y := E) C1 C2 := by
  have hneg_closed : IsClosed (-C2) := by
    simpa [Set.mem_neg] using hC2_closed.preimage continuous_neg
  have hcommon_lineality_neg :
      ∀ ⦃z : E⦄, z ∈ 0⁺[𝕜] C1 → -z ∈ 0⁺[𝕜] (-C2) → z ∈ lin[𝕜](-C2) := by
    intro z hzC1 hzC2
    have hzC2' : z ∈ 0⁺[𝕜] C2 :=
      Set.neg_mem_recessionCone_neg_iff.mp hzC2
    have hz_lineal : z ∈ lin[𝕜](C2) :=
      hcommon_lineality hzC1 hzC2'
    rw [Set.mem_lineal_iff] at hz_lineal ⊢
    constructor
    · exact Set.neg_mem_recessionCone_neg_iff.mpr hz_lineal.2
    · simpa using Set.neg_mem_recessionCone_neg_iff.mpr hz_lineal.1
  have hsub_closed : IsClosed (C1 - C2) := by
    have hsum_closed : IsClosed (C1 + (-C2 : Set E)) :=
      Set.IsPolyhedral.isClosed_add_of_closed_of_opposite_recession_imp_lineality
        hC1_poly
        hC2_conv.neg hneg_closed hcommon_lineality_neg
    simpa [sub_eq_add_neg] using hsum_closed
  have hzero_notMem_sub : (0 : E) ∉ C1 - C2 := by
    intro h0
    rcases Set.mem_sub.mp h0 with ⟨x1, hx1, x2, hx2, hsub⟩
    exact hdisj.le_bot ⟨hx1, by simpa [sub_eq_zero.mp hsub] using hx2⟩
  refine
    (exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
      hC1_poly.convex hC1_nonempty hC2_conv hC2_nonempty).2 ?_
  simpa [hsub_closed.closure_eq] using hzero_notMem_sub

end

/-! ### Theorem_20_3 (from Chap04) -/
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
