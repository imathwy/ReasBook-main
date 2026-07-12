import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped Pointwise PolarCone Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type (max u v)}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜]
variable {f : E → WithBotTop 𝕜} {K : Set E}

local notation "ri(" C ")" => intrinsicInterior 𝕜 C
local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "convexDual" => (f⋆ : EStar → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 31.4 is Fenchel duality for minimization over a closed convex cone,
  together with the branchwise attainment conclusions, the polyhedral weakening of the
  qualifications, and the equality-case criterion.
- `core/canonical`: the relevant project owners are the paired-duality ambient
  `HasLinearPairing E EStar 𝕜`, `Function.IsClosedProperConvex`, the Fenchel conjugate owner
  `convexConjugate` with notation `f⋆ : EStar → WithBotTop 𝕜`, Rockafellar's
  effective-domain notation `riDom[𝕜](·)`, the source-facing polar-cone notation
  `Kᵒ[𝕜] : Set EStar`, `Set.IsPolyhedral`, `IsMinOn`, and the Chapter 23 pairing-valued
  subgradient owner `_root_.subdifferentialAt`, exposed here through the notation
  `∂[EStar]f(x)`.
- `bridge/view`: the source dual cone `K* = {x* | ⟪x, x*⟫ ≥ 0 for all x ∈ K}` is the reusable
  Chapter 14 bridge `K∗[𝕜]`, defined there as the sign-twisted polar cone `-Kᵒ`.

Domain-style sampling used here:

- `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification`,
  `exists_isMaxOn_concaveConjugate_sub_convexConjugate_of_riDom_inter_nonempty`, and
  `exists_isMinOn_sub_of_dual_riDom_inter_nonempty` from `Theorem_31_1`;
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone` from `Theorem_14_1`;
- `Set.IsPolyhedral.isClosed_of_finiteDimensional` from `Definition_2_1_2`;
- `_root_.subdifferentialAt` and the notation `∂[Y]f(x)` from `Definition_23_0_6`.

Primitive data vs derived API:

- primitive inputs: the paired primal/dual ambient `E × EStar`, the closed proper convex
  function `f`, the cone `K`, and the qualification conditions on `riDom[𝕜](f)` and
  `riDom[𝕜](f⋆)` relative to `K` and the source dual cone `K∗[𝕜]`;
- derived API: the zero-duality-gap identity for the infima of `f` on `K` and of `f⋆` on
  `K∗[𝕜]`, the branchwise attainment statements in owner form `IsMinOn`, the polyhedral
  weakening of the qualification hypotheses, and the equality-case criterion expressed through
  the pairing-level subgradient owner plus the direct complementary-slackness conjunction.

Layer target: `source-facing`. The theorem remains directly about minimization of `f` over `K`
and of `f⋆` over the source dual cone `K∗[𝕜]`, rather than being repackaged as a new local
structure.
-/

-- Proof sketch: apply Theorem 31.1 to `g = -δ[𝕜](· | K)`. Theorem 14.1 identifies the convex
-- conjugate of `δ[𝕜](· | K)` with `δ[𝕜](· | Kᵒ)`, so the concave conjugate of `g` is the
-- negative indicator of the source dual cone `K∗[𝕜]`.
/-- Theorem 31.4: if `f` is closed proper convex and `K` is a nonempty closed convex cone, then
`inf_K f` equals the negative of `inf_{K∗[𝕜]} f⋆` whenever either `riDom[𝕜](f)` meets `ri(K)` or
`riDom[𝕜](f⋆)` meets `ri(K∗[𝕜])`. -/
theorem iInf_on_cone_eq_neg_iInf_on_dualCone_of_fenchel_cone_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (hqual :
      Set.Nonempty (riDom[𝕜](f) ∩ ri(K)) ∨
        Set.Nonempty (riDom[𝕜](convexDual) ∩ ri(K∗[𝕜]))) :
    (⨅ x : K, f x) = -(⨅ xStar : (K∗[𝕜] : Set EStar), convexDual xStar) := sorry

-- Proof sketch: specialize the attainment clause (a) of Theorem 31.1 to
-- `g = -δ[𝕜](· | K)`, then rewrite the dual objective by the same sign-twisted indicator
-- identity used in the main theorem.
/-- Under the primal relative-interior qualification, the infimum of `f⋆` over `K∗[𝕜]`
is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_dualCone_of_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK : Set.IsConvexCone 𝕜 K)
    (hqual : Set.Nonempty (riDom[𝕜](f) ∩ ri(K))) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar), IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: specialize the attainment clause (b) of Theorem 31.1 to the indicator-cone
-- choice `g = -δ[𝕜](· | K)`. After rewriting the primal objective as the restriction of `f` to
-- `K`, the resulting minimizer is exactly a point of `K` attaining the infimum of `f` there.
/-- Under the dual relative-interior qualification, the infimum of `f` over `K` is attained. -/
theorem exists_mem_isMinOn_on_cone_of_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (hqual : Set.Nonempty (riDom[𝕜](convexDual) ∩ ri(K∗[𝕜]))) :
    ∃ x ∈ K, IsMinOn f K x := sorry

-- Proof sketch: apply the Chapter 31 equality-case criterion for the indicator-cone perturbation
-- `g = -δ[𝕜](· | K)` on the pairing-level dual carrier.
/-- The attainment form of the optimality criterion in Theorem 31.4 is equivalent to the source
subgradient, dual-feasibility, and complementary-slackness conditions. -/
theorem optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_closed : IsClosed K) (hK : Set.IsConvexCone 𝕜 K)
    (x : E) (xStar : EStar) :
    IsMinOn f K x ∧
      IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar ∧
      f x = -convexDual xStar ↔
      xStar ∈ ∂[EStar]f(x) ∧
        x ∈ K ∧ xStar ∈ (K∗[𝕜] : Set EStar) ∧ ⟪x, xStar⟫ₚ = (0 : 𝕜) := sorry

section

variable [CompleteSpace 𝕜]

-- Proof sketch: for a polyhedral cone, the relative interior conditions in Theorem 31.4 may be
-- replaced by ordinary membership on the cone side and on the source-dual-cone side.
/-- If `K` is polyhedral, the qualification clauses in Theorem 31.4 may be weakened by replacing
`ri(K)` and `ri(K∗[𝕜])` with `K` and `K∗[𝕜]`. -/
theorem iInf_on_cone_eq_neg_iInf_on_dualCone_of_polyhedral_fenchel_cone_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual :
      Set.Nonempty (riDom[𝕜](f) ∩ K) ∨
        Set.Nonempty (riDom[𝕜](convexDual) ∩ K∗[𝕜])) :
    (⨅ x : K, f x) = -(⨅ xStar : (K∗[𝕜] : Set EStar), convexDual xStar) := sorry

-- Proof sketch: use the same polyhedral weakening of clause (a), then apply the dual-attainment
-- argument above. Closedness of `K` is derived from `hK_poly.isClosed_of_finiteDimensional`.
/-- If `K` is polyhedral and `riDom[𝕜](f)` meets `K`, then the infimum of `f⋆` over `K∗[𝕜]`
is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_dualCone_of_polyhedral_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual : Set.Nonempty (riDom[𝕜](f) ∩ K)) :
    ∃ xStar ∈ (K∗[𝕜] : Set EStar), IsMinOn convexDual (K∗[𝕜] : Set EStar) xStar := sorry

-- Proof sketch: use the polyhedral weakening of clause (b), then repeat the primal-attainment
-- specialization of Theorem 31.1 for the indicator-cone perturbation.
/-- If `K` is polyhedral and `riDom[𝕜](f⋆)` meets `K∗[𝕜]`, then the infimum of `f` over `K`
is attained. -/
theorem exists_mem_isMinOn_on_cone_of_polyhedral_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hK_nonempty : K.Nonempty) (hK : Set.IsConvexCone 𝕜 K)
    (hK_poly : K.IsPolyhedral 𝕜)
    (hqual : Set.Nonempty (riDom[𝕜](convexDual) ∩ K∗[𝕜])) :
    ∃ x ∈ K, IsMinOn f K x := sorry

end

end
