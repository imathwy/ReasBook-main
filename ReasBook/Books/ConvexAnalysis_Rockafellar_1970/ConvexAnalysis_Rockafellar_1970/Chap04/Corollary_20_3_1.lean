import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_4

-- Declarations for this item will be appended below by the statement pipeline.

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
